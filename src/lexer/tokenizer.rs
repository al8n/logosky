use core::{marker::PhantomData, mem::MaybeUninit};

use crate::{
  token::RefLexed,
  utils::{Span, Spanned},
};

use either::Either;

use super::*;

/// Iterators for [`Tokenizer`]
pub mod iter;

/// A zero-copy token stream adapter that bridges Logos and Chumsky.
///
/// `Tokenizer` is the core integration layer between [Logos](https://github.com/maciejhirsz/logos)
/// lexical analysis and [Chumsky](https://github.com/zesterer/chumsky) parser combinators.
/// It efficiently wraps a Logos token source and implements all necessary Chumsky input traits,
/// allowing you to use Chumsky parsers directly on Logos tokens.
///
/// # Zero-Copy Design
///
/// `Tokenizer` doesn't allocate or copy tokens. Instead, it maintains a cursor position
/// and calls Logos on-demand as the parser consumes tokens. This makes it efficient for
/// large inputs and streaming scenarios.
///
/// # State Management
///
/// For stateful lexers (those with non-`()` `Extras`), `Tokenizer` maintains the lexer
/// state and passes it through token-by-token. This allows for context-sensitive lexing
/// patterns. Because the adapter clones `Extras` each time it polls Logos, it is best to
/// keep your state `Copy` or otherwise cheap to clone. If you need heavy state, consider
/// storing handles (e.g. `Arc`) inside `Extras` so clones stay inexpensive.
///
/// # Type Parameters
///
/// - `'a`: The lifetime of the input source
/// - `T`: The token type implementing [`Token<'a>`]
///
/// # Implemented Traits
///
/// This type implements all core Chumsky input traits:
/// - [`Input`](chumsky::input::Input) - Basic input stream functionality
/// - [`ValueInput`](chumsky::input::ValueInput) - Token-by-token consumption
/// - [`SliceInput`](chumsky::input::SliceInput) - Slice extraction from source
/// - [`ExactSizeInput`](chumsky::input::ExactSizeInput) - Known input length
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust,ignore
/// use logosky::{Token, Tokenizer, TokenExt};
/// use logos::Logos;
/// use chumsky::prelude::*;
///
/// #[derive(Logos, Debug, Clone, Copy, PartialEq)]
/// #[logos(skip r"[ \t\n]+")]
/// enum MyTokens {
///     #[regex(r"[0-9]+")]
///     Number,
///     #[token("+")]
///     Plus,
/// }
///
/// // Create a token stream from input
/// let input = "42 + 13";
/// let stream = MyToken::lexer(input); // Returns Tokenizer<'_, MyToken>
///
/// // Use with Chumsky parsers
/// let parser = any().repeated().collect::<Vec<_>>();
/// let tokens = parser.parse(stream).into_result();
/// ```
///
/// ## Stateful Lexing
///
/// ```rust,ignore
/// #[derive(Default, Clone)]
/// struct LexerState {
///     brace_count: usize,
/// }
///
/// #[derive(Logos, Debug, Clone, Copy)]
/// #[logos(extras = LexerState)]
/// enum MyTokens {
///     #[token("{", |lex| lex.extras.brace_count += 1)]
///     LBrace,
///     #[token("}", |lex| lex.extras.brace_count -= 1)]
///     RBrace,
/// }
///
/// let input = "{ { } }";
/// let initial_state = LexerState::default();
/// let stream = Tokenizer::with_state(input, initial_state);
/// ```
///
/// ## Cloning and Backtracking
///
/// Tokenizer supports cloning (when the token type and extras are Clone/Copy),
/// which is essential for Chumsky's backtracking:
///
/// ```rust,ignore
/// let stream = MyToken::lexer(input);
/// let checkpoint = stream.clone(); // Save position for backtracking
///
/// // Try to parse something
/// if let Err(_) = try_parser.parse(stream) {
///     // Backtrack by using the cloned stream
///     alternative_parser.parse(checkpoint);
/// }
/// ```
pub struct Tokenizer<'a, T: Token<'a>, C = ()> {
  pub(crate) input: &'a <T::Logos as Logos<'a>>::Source,
  pub(crate) state: <T::Logos as Logos<'a>>::Extras,
  pub(crate) cursor: usize,
  pub(crate) cache: C,
}

impl<'a, T, C> Clone for Tokenizer<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      input: self.input,
      state: self.state.clone(),
      cursor: self.cursor,
      cache: self.cache.clone(),
    }
  }
}

impl<'a, T, C> Copy for Tokenizer<'a, T, C>
where
  T: Token<'a> + Copy,
  <T::Logos as Logos<'a>>::Extras: Copy,
  <T::Logos as Logos<'a>>::Error: Copy,
  C: Copy,
{
}

impl<'a, T, C> core::fmt::Debug for Tokenizer<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
  C: core::fmt::Debug,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Tokenizer")
      .field("input", &self.input)
      .field("state", &self.state)
      .field("cursor", &self.cursor)
      .field("cache", &self.cache)
      .finish()
  }
}

impl<'a, T> Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Default,
{
  /// Creates a new lexer from the given input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(input: &'a <T::Logos as Logos<'a>>::Source) -> Self {
    Self::with_state(input, <T::Logos as Logos<'a>>::Extras::default())
  }
}

impl<'a, T: Token<'a>> Tokenizer<'a, T> {
  /// Creates a new lexer from the given input and state.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_state(
    input: &'a <T::Logos as Logos<'a>>::Source,
    state: <T::Logos as Logos<'a>>::Extras,
  ) -> Self {
    Self {
      input,
      state,
      cursor: 0,
      cache: (),
    }
  }
}

impl<'a, T: Token<'a>, C> Tokenizer<'a, T, C> {
  /// Returns the cache of the tokenizer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn cache(&self) -> &C {
    &self.cache
  }

  /// Returns a reference to the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn input(&self) -> &<T::Logos as Logos<'a>>::Source {
    self.input
  }

  /// Returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn iter(&mut self) -> iter::Iter<'a, '_, T, C> {
    iter::Iter::new(self)
  }

  /// Consumes the lexer and returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn into_iter(self) -> iter::IntoIter<'a, T, C> {
    iter::IntoIter::new(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn lexer(&self) -> logos::Lexer<'a, T::Logos>
  where
    <T::Logos as Logos<'a>>::Extras: Clone,
  {
    let mut lexer = logos::Lexer::<T::Logos>::with_extras(self.input, self.state.clone());
    lexer.bump(self.cursor);
    lexer
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn set_cursor(&mut self, new: usize) {
    self.cursor = new.min(self.input.len());
  }
}

impl<'a, T: Token<'a>, C> Tokenizer<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Cache<'a, T>,
{
  // /// Peeks the tokens until find
  // pub fn peek_until(&mut self, pred: impl Fn(&Lexed<'a, T>) -> bool) -> Option<Lexed<'a, T>> {
  //   if let Some(cached_token) = self.cache.peek() {
  //     return Some(cached_token.data.clone());
  //   }

  //   let state = self.state.clone();
  //   let mut lexer = logos::Lexer::<T::Logos>::with_extras(self.input, state);
  //   lexer.bump(self.cursor);
  //   Lexed::lex(&mut lexer).map(|tok| {
  //     self.cache_token(lexer.span().into(), lexer.extras.clone(), tok)
  //   })
  // }

  /// Consumes one token from the peeked tokens and returns it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_one(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    let tok = self.cache.pop_front()?;
    let (tok, extras) = tok.into_components();
    self.set_cursor(tok.span().end());
    self.state = extras;
    Some(tok)
  }

  /// Skips one token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_one(&mut self) -> bool {
    if let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, _lexed) = spanned_lexed.into_components();
      self.set_cursor(span.end());
      self.state = extras;
      true
    } else {
      self.next().is_some()
    }
  }

  /// Skips error tokens until a valid token is found or the end of input is reached.
  ///
  /// Returns the number of skipped error tokens.
  pub fn skip_errors(&mut self) -> usize {
    let mut num = 0;
    while let Some(tok) = self.cache.pop_front_if(|t| t.is_error()) {
      self.set_cursor(tok.token().span().end());
      self.state = tok.extras;
      num += 1;
    }

    if num > 0 {
      return num;
    }

    let mut lexer = self.lexer();
    while let Some(lexed) = Lexed::<T>::lex_spanned(&mut lexer) {
      let (span, lexed) = lexed.into_components();

      match lexed {
        Lexed::Token(tok) => {
          // If the cache is full, we just drop the token
          let _ = self.cache.push_back(CachedToken::new(
            Spanned::new(span, Lexed::Token(tok)),
            lexer.extras.clone(),
          ));
          break;
        }
        Lexed::Error(_) => {
          self.set_cursor(lexer.span().end);
          num += 1
        }
      }
    }

    if num > 0 {
      self.state = lexer.extras.clone();
    }

    num
  }

  /// Peeks the next token without advancing the cursor.
  #[inline]
  pub fn peek_one(&mut self) -> Option<Spanned<Either<RefLexed<'a, '_, T>, Lexed<'a, T>>>> {
    let maybe_lexed = if self.cache.is_empty() {
      let mut lexer = self.lexer();
      Lexed::lex_spanned(&mut lexer).map(|tok| {
        let (span, tok) = tok.into_components();
        let cached = CachedToken::new(Spanned::new(span, tok), lexer.extras.clone());
        (span, cached)
      })
    } else {
      None
    };

    if let Some((span, cached)) = maybe_lexed {
      Some(Spanned::new(
        span,
        match self.cache.push_back(cached) {
          Ok(tok) => Either::Left(tok),
          Err(tok) => Either::Right(tok.token.data),
        },
      ))
    } else {
      self.cache.peek_one().map(|t| t.token().as_ref().map_data(|t| Either::Left(t.as_ref())))
    }
  }

  /// Peeks the next token without advancing the cursor.
  #[inline]
  pub fn peek(&mut self, buf: &mut [MaybeUninit<Spanned<Either<RefLexed<'a, '_, T>, Lexed<'a, T>>>>]) -> &mut [Spanned<Either<RefLexed<'a, '_, T>, Lexed<'a, T>>>] {
    let mut filled = 0;

    // First, fill from cache
    while filled < buf.len() {
      if let Some(cached) = self.cache.peek_one() {
        buf[filled].write(cached.map_data(Either::Left));
        filled += 1;
      } else {
        break;
      }
    }

    // Then, lex more tokens if needed
    let mut lexer = self.lexer();
    while filled < buf.len() {
      if let Some(lexed) = Lexed::lex_spanned(&mut lexer) {
        let (span, lexed) = lexed.into_components();
        let cached = CachedToken::new(Spanned::new(span, lexed), lexer.extras.clone());
        match self.cache.push_back(cached) {
          Ok(tok) => {
            buf[filled].write(tok.map_data(Either::Left));
          }
          Err(tok) => {
            buf[filled].write(tok.token.data.map_data(Either::Right));
          }
        }
        filled += 1;
      } else {
        break;
      }
    }

    // Safety: We have initialized `filled` elements in `buf`
    unsafe { core::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut Spanned<Either<RefLexed<'a, '_, T>, Lexed<'a, T>>>, filled) }
  
  }

  /// Saves the current state of the tokenizer as a checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn save(&self) -> Checkpoint<'a, '_, T> {
    Checkpoint::new(self.cursor(), self.state.clone())
  }

  /// Returns the current cursor of the tokenizer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn cursor(&self) -> Cursor<'a, '_, T> {
    Cursor::new(self.cursor)
  }

  /// Rewinds the tokenizer to the given checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn rewind(&mut self, checkpoint: Checkpoint<'a, '_, T>) {
    self.cache.rewind(&checkpoint);
    self.set_cursor(checkpoint.cursor().cursor);
    self.state = checkpoint.state;
  }

  /// Advances the cursor and returns the next valid token, emit non-fatal errors, fatal errors are returned and stop the process.
  pub fn next_valid_with<E>(
    &mut self,
    mut emitter: E,
    f: impl Fn(<T::Logos as Logos<'a>>::Error) -> E::Error,
  ) -> Result<Option<Spanned<T>>, E::Error>
  where
    E: Emitter<'a, T>,
  {
    // First, consume from cache if available
    while let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, lexed) = spanned_lexed.into_components();
      self.set_cursor(span.end());
      self.state = extras;
      match lexed {
        Lexed::Token(t) => return Ok(Some(Spanned::new(span, t))),
        Lexed::Error(e) => {
          emitter.emit(Spanned::new(span, f(e)))?;
          continue;
        }
      }
    }

    // then, construct a lexer and lex until a valid token is found
    let mut lexer = self.lexer();

    while let Some(lexed) = Lexed::lex_spanned(&mut lexer) {
      let (span, lexed) = lexed.into_components();
      self.set_cursor(lexer.span().end);
      self.state = lexer.extras.clone();

      match lexed {
        Lexed::Token(t) => return Ok(Some(Spanned::new(span, t))),
        Lexed::Error(e) => {
          emitter.emit(Spanned::new(span, f(e)))?;
          continue;
        }
      }
    }

    Ok(None)
  }

  /// Advances the cursor and returns the next valid token, emit non-fatal errors, fatal errors are returned and stop the process.
  pub fn next_valid<E>(&mut self, emitter: E) -> Result<Option<Spanned<T>>, E::Error>
  where
    E: Emitter<'a, T>,
    E::Error: From<<T::Logos as Logos<'a>>::Error>,
  {
    self.next_valid_with(emitter, From::from)
  }

  /// Advances the cursor and returns the next token.
  #[allow(clippy::should_implement_trait)]
  pub fn next(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    if let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, lexed) = spanned_lexed.into_components();
      self.set_cursor(span.end());
      self.state = extras;
      return Some(Spanned::new(span, lexed));
    }

    let state = self.state.clone();
    let mut lexer = logos::Lexer::<T::Logos>::with_extras(self.input, state);
    lexer.bump(self.cursor);
    Lexed::lex_spanned(&mut lexer).inspect(|_| {
      self.set_cursor(lexer.span().end);
      self.state = lexer.extras.clone();
    })
  }

  // #[cfg_attr(not(tarpaulin), inline(always))]
  // pub(crate) fn next_at(&mut self, cursor: &mut usize) -> Option<Spanned<Lexed<'a, T>>> {
  //   let state = self.state.clone();
  //   let mut lexer = logos::Lexer::<T::Logos>::with_extras(self.input, state);
  //   lexer.bump(*cursor);
  //   Lexed::lex_spanned(&mut lexer).inspect(|_| {
  //     *cursor = lexer.span().end;
  //     self.state = lexer.extras.clone();
  //   })
  // }
}

/// A checkpoint for the tokenizer.
pub struct Checkpoint<'a, 's, T: Token<'a>> {
  cursor: Cursor<'a, 's, T>,
  state: <T::Logos as Logos<'a>>::Extras,
  _m: PhantomData<fn(&'s ()) -> &'s ()>,
}

impl<'a, 's, T: Token<'a>> Checkpoint<'a, 's, T> {
  /// Creates a new checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(cursor: Cursor<'a, 's, T>, state: <T::Logos as Logos<'a>>::Extras) -> Self {
    Self {
      cursor,
      state,
      _m: PhantomData,
    }
  }

  /// Returns the cursor of the checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn cursor(&self) -> Cursor<'a, 's, T> {
    self.cursor
  }

  /// Returns the state of the checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn state(&self) -> &<T::Logos as Logos<'a>>::Extras {
    &self.state
  }
}

/// A cursor for the tokenizer.
pub struct Cursor<'a, 's, T: Token<'a>> {
  cursor: usize,
  _m: PhantomData<fn(&'s ()) -> &'s ()>,
  _t: PhantomData<fn(&'a T) -> &'a T>,
}

impl<'a, T: Token<'a>> core::fmt::Debug for Cursor<'a, '_, T> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "Cursor({})", self.cursor)
  }
}

impl<'a, T: Token<'a>> Clone for Cursor<'a, '_, T> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, T: Token<'a>> Copy for Cursor<'a, '_, T> {}

impl<'a, T: Token<'a>> Cursor<'a, '_, T> {
  /// Creates a new cursor.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(cursor: usize) -> Self {
    Self {
      cursor,
      _m: PhantomData,
      _t: PhantomData,
    }
  }

  /// Returns the cursor position.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn position(&self) -> usize {
    self.cursor
  }
}

/// An emitter for errors.
pub trait Emitter<'a, T: Token<'a>> {
  /// The error type emitted.
  type Error;

  /// Emits a non-fatal error, if this error is a fatal error, then returns the error back.
  fn emit(&mut self, err: Spanned<Self::Error>) -> Result<(), Self::Error>;
}

impl<'a, T, U> Emitter<'a, T> for &mut U
where
  T: Token<'a>,
  U: Emitter<'a, T>,
{
  type Error = U::Error;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit(&mut self, err: Spanned<Self::Error>) -> Result<(), Self::Error> {
    (**self).emit(err)
  }
}

/// A cached token with its associated extras.
pub struct CachedToken<'a, T: Token<'a>> {
  token: Spanned<Lexed<'a, T>>,
  extras: <T::Logos as Logos<'a>>::Extras,
}

impl<'a, T: Token<'a>> Clone for CachedToken<'a, T>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      token: self.token.clone(),
      extras: self.extras.clone(),
    }
  }
}

impl<'a, T: Token<'a>> CachedToken<'a, T> {
  /// Creates a new cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(token: Spanned<Lexed<'a, T>>, extras: <T::Logos as Logos<'a>>::Extras) -> Self {
    Self { token, extras }
  }

  /// Returns a reference to the token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn token(&self) -> &Spanned<Lexed<'a, T>> {
    &self.token
  }

  /// Consumes the cached token and returns the lexed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_token(self) -> Spanned<Lexed<'a, T>> {
    self.token
  }

  /// Returns a reference to the extras.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn extras(&self) -> &<T::Logos as Logos<'a>>::Extras {
    &self.extras
  }

  /// Consumes the cached token and returns the extras.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Spanned<Lexed<'a, T>>, <T::Logos as Logos<'a>>::Extras) {
    (self.token, self.extras)
  }
}

/// A cache for peeked tokens.
pub trait Cache<'a, T: Token<'a>> {
  /// Returns `true` if the cache is empty.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the number of cached tokens.
  fn len(&self) -> usize;

  /// Rewinds to the given checkpoint.
  fn rewind(&mut self, checkpoint: &Checkpoint<'a, '_, T>);

  /// Caches one token.
  ///
  /// If the cache is full, returns the token back, otherwise returns a reference to the token.
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T>,
  ) -> Result<RefLexed<'a, '_, T>, CachedToken<'a, T>>;

  /// Pops one cached token.
  #[allow(clippy::type_complexity)]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T>>;

  /// Pops one cached token.
  #[allow(clippy::type_complexity)]
  fn pop_front_if<F>(&mut self, predicate: F) -> Option<CachedToken<'a, T>>
  where
    F: Fn(&Spanned<RefLexed<'a, '_, T>>) -> bool,
  {
    if let Some(peeked) = self.first() {
      if predicate(&peeked) {
        return self.pop_front();
      }
    }
    None
  }

  /// Peeks one cached token without removing it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn peek_one<'c>(&'c self) -> Option<&CachedToken<'a, T>>
  where
    'a: 'c,
  {
    let mut buf: [MaybeUninit<&CachedToken<'a, T>>; 1] = [MaybeUninit::uninit()];
    self.peek(&mut buf).first().copied()
  }

  /// Try to peeks exactly cached tokens without removing them.
  ///
  /// The provided buffer will be filled with the peeked tokens, and the returned slice will contain only the initialized tokens.
  #[allow(clippy::mut_from_ref)]
  fn peek(
    &self,
    buf: &mut [MaybeUninit<&CachedToken<'a, T>>],
  ) -> &mut [&CachedToken<'a, T>];

  /// Pushes a batch of tokens into the cache.
  ///
  /// # Note
  ///
  /// If the cache is full, returns an iterator over the tokens that not be cached.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_many<'c>(
    &'c mut self,
    toks: impl Iterator<Item = CachedToken<'a, T>> + 'c,
  ) -> impl Iterator<Item = CachedToken<'a, T>> + 'c {
    toks.filter_map(move |tok| self.push_back(tok).err())
  }

  /// Returns the first cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn first<'c>(&'c self) -> Option<Spanned<RefLexed<'a, 'c, T>>>
  where
    'a: 'c,
  {
    self.first_with_extras().map(|(t, _)| t)
  }

  /// Returns the first cached token and its extras.
  #[allow(clippy::type_complexity)]
  fn first_with_extras<'c>(
    &'c self,
  ) -> Option<(
    Spanned<RefLexed<'a, 'c, T>>,
    &'c <T::Logos as Logos<'a>>::Extras,
  )>;

  /// Returns the last cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn last<'c>(&'c self) -> Option<Spanned<RefLexed<'a, 'c, T>>>
  where
    'a: 'c,
  {
    self.last_with_extras().map(|(t, _)| t)
  }

  /// Returns the last cached token and its extras.
  #[allow(clippy::type_complexity)]
  fn last_with_extras<'c>(
    &'c self,
  ) -> Option<(
    Spanned<RefLexed<'a, 'c, T>>,
    &'c <T::Logos as Logos<'a>>::Extras,
  )>;

  /// Returns the span of the cached tokens, from the start of the first to the end of the last.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span(&self) -> Option<Span> {
    match (self.first(), self.last()) {
      (Some(first), Some(last)) => Some(Span::new(first.span().start(), last.span().end())),
      _ => None,
    }
  }

  /// Returns the span of the first cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_first(&self) -> Option<Span> {
    self.first().map(|t| t.span())
  }

  /// Returns the span of the last cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_last(&self) -> Option<Span> {
    self.last().map(|t| t.span())
  }
}

impl<'a, T> Cache<'a, T> for ()
where
  T: Token<'a>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    0
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn peek(
    &self,
    _: &mut [MaybeUninit<Spanned<RefLexed<'a, '_, T>>>],
  ) -> &mut [Spanned<RefLexed<'a, '_, T>>] {
    &mut []
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn rewind(&mut self, _: &Checkpoint<'a, '_, T>) {}

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T>,
  ) -> Result<RefLexed<'a, '_, T>, CachedToken<'a, T>> {
    Err(tok)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn first_with_extras<'c>(
    &'c self,
  ) -> Option<(
    Spanned<RefLexed<'a, 'c, T>>,
    &'c <T::Logos as Logos<'a>>::Extras,
  )> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn last_with_extras<'c>(
    &'c self,
  ) -> Option<(
    Spanned<RefLexed<'a, 'c, T>>,
    &'c <T::Logos as Logos<'a>>::Extras,
  )> {
    None
  }
}
