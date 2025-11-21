use core::{marker::PhantomData, mem::MaybeUninit};

use mayber::MaybeRef;

use crate::utils::{Span, Spanned};

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
  /// Consumes one token from the peeked tokens and returns the consumed token if any, the cursor is advanced.
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[allow(clippy::type_complexity)]
  pub fn consume_one(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    let tok = self.cache.pop_front()?;
    let (tok, extras): (Spanned<Lexed<'a, T>>, _) = tok.into_components();
    self.set_cursor(tok.span().end());
    self.state = extras;
    Some(tok)
  }

  /// Consumes tokens from cache until the predicate returns `true`, the cursor is advanced to the end of the last consumed token.
  /// 
  /// Returns the last consumed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_until<F>(&mut self, mut f: F) -> Option<Spanned<Lexed<'a, T>>>
  where
    F: FnMut(&CachedToken<'a, T>) -> bool,
  {
    let mut last = None;
    // pop from cache if not matching
    while let Some(tok) = self.cache.pop_front_if(|t| !f(t))  { 
      self.set_cursor(tok.token().span().end());
      let (tok, state) = tok.into_components();
      self.state = state;
      last = Some(tok);
    }

    last
  }

  /// Consumes tokens from cache while the predicate returns `true`, the cursor is advanced to the end of the last consumed token.
  /// 
  /// Returns the last consumed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_while<F>(&mut self, mut f: F) -> Option<Spanned<Lexed<'a, T>>>
  where
    F: FnMut(&CachedToken<'a, T>) -> bool,
  {
    self.consume_until(|t| !f(t))
  }

  /// Consumes all cached tokens, the cursor is advanced to the end of the last cached token.
  /// 
  /// Returns the last consumed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_all(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    let last = self.cache.pop_back()?;
    self.cache.clear();
    let (tok, extras): (Spanned<Lexed<'a, T>>, _) = last.into_components();
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

  /// Skips tokens until a valid token is found or the end of input is reached.
  /// 
  /// Returns the first valid token found, but without consuming it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_until<F>(&mut self, mut pred: F) -> Option<MaybeRef<'_, CachedToken<'a, T>>>
  where
    F: FnMut(&Spanned<Lexed<'a, T>>) -> bool,
  {
    // pop from cache if not matching
    while let Some(tok) = self.cache.pop_front_if(|t| !pred(t.token()))  { 
      self.set_cursor(tok.token().span().end());
      self.state = tok.state;
    }

    // as the matched token will not be consumed, we just peek it
    match !self.cache.is_empty() {
      // If the matched token is in cache, return it
      true => self.cache.peek_one(),
      // Otherwise, let's skip the input
      false => {
        let mut lexer = self.lexer();
        let mut end = self.cursor;
        let mut state = self.state.clone();

        while let Some(lexed) = Lexed::<T>::lex_spanned(&mut lexer) {
          // if the token matches, we cache it and return it
          if pred(&lexed) {
            let ct = CachedToken::new(
              lexed,
              lexer.extras.clone(),
            );
            self.set_cursor(end);
            self.state = state;

            return match self.cache.push_back(ct) {
              Ok(tok) => Some(MaybeRef::Ref(tok)),
              Err(ct) => Some(MaybeRef::Owned(ct)),
            }
          }

          end = lexer.span().end;
          state = lexer.extras.clone();
        }

        // No matched token found, we just update the cursor and state
        self.set_cursor(lexer.span().end);
        self.state = lexer.extras;

        None
      },
    }
  }

  /// Skips tokens while the predicate returns `true`.
  /// 
  /// Returns the first token that does not match the predicate, but without consuming it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_while<F>(&mut self, mut pred: F) -> Option<MaybeRef<'_, CachedToken<'a, T>>>
  where
    F: FnMut(&Spanned<Lexed<'a, T>>) -> bool,
  {
    self.skip_until(|t| !pred(t))
  }

  /// Skips error tokens until a valid token is found or the end of input is reached.
  ///
  /// Returns the number of skipped error tokens.
  pub fn skip_until_valid(&mut self) -> Option<MaybeRef<'_, CachedToken<'a, T>>> {
    self.skip_until(|t| matches!(t.data, Lexed::Token(_)))
  }

  /// a
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_until_with_emitter<F, E>(&mut self, mut pred: F, mut emitter: E) -> Result<Option<MaybeRef<'_, CachedToken<'a, T>>>, E::Error>
  where
    E: Emitter<'a, T>,
    F: FnMut(Spanned<&T>, &mut E) -> bool,
  {
    // pop from cache if not matching
    while let Some(tok) = self.cache.pop_front_if(|t| {
      let span = t.token().span();
      match t.token().data() {
        Lexed::Token(tok) => !pred(Spanned::new(span, tok), &mut emitter),
        Lexed::Error(_) => true,
      }
    }) {
      let span = tok.token().span();
      self.set_cursor(span.end());
      self.state = tok.state;
      if let Lexed::Error(e) = tok.token.into_data() {
        emitter.emit_token_error(Spanned::new(span, e))?;
      }
    }

    // as the matched token will not be consumed, we just peek it
    match !self.cache.is_empty() {
      // If the matched token is in cache, return it
      true => Ok(self.cache.peek_one()),
      // Otherwise, let's skip the input
      false => {
        let mut lexer = self.lexer();

        let mut end = self.cursor;
        let mut state = self.state.clone();

        while let Some(Spanned { span, data: tok }) = Lexed::<T>::lex_spanned(&mut lexer) {
          match tok {
            Lexed::Error(err) => {
              match emitter.emit_token_error(Spanned::new(span, err)) {
                Ok(_) => {
                  end = lexer.span().end;
                  state = lexer.extras.clone();
                },
                Err(e) => {
                  self.set_cursor(lexer.span().end);
                  self.state = lexer.extras;
                  return Err(e)
                },
              }
            }
            Lexed::Token(tok) => {
              let tok = Spanned::new(span, tok);
              // if the token matches, we cache it and return it
              if pred(tok.as_ref(), &mut emitter) {
                let ct = CachedToken::new(
                  tok.map_data(Lexed::Token),
                  lexer.extras,
                );
                self.set_cursor(end);
                self.state = state;
                return Ok(match self.cache.push_back(ct) {
                  Ok(tok) => Some(MaybeRef::Ref(tok)),
                  Err(ct) => Some(MaybeRef::Owned(ct)),
                })
              }

              end = lexer.span().end;
              state = lexer.extras.clone();
            },
          }
        }

        // No matched token found, we just update the cursor and state
        self.set_cursor(lexer.span().end);
        self.state = lexer.extras;

        Ok(None)
      },
    }
  }

  /// Peeks the next token without advancing the cursor.
  #[inline]
  pub fn peek_one(&mut self) -> Option<MaybeRef<'_, CachedToken<'a, T>>> {
    let mut buf: [MaybeUninit<MaybeRef<'_, CachedToken<'a, T>>>; 1] = [MaybeUninit::uninit()];
    let feed = self.peek(&mut buf);
    if feed.is_empty() {
      return None;
    }

    // SAFETY: We just checked that the buffer is not empty, so the first element is initialized.
    buf.into_iter().next().map(|m| unsafe { m.assume_init() })
  }

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

  /// Try to peeks tokens to fill the provided buffer, if not enough tokens are cached, lex more tokens to fill the buffer.
  /// 
  /// The returned slice will contain only the initialized tokens.
  #[inline]
  pub fn peek(&mut self, buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T>>>]) -> &mut [MaybeRef<'_, CachedToken<'a, T>>] {
    let buf_len = buf.len();
    let mut in_cache = self.cache.len();
    let mut want = buf_len.saturating_sub(in_cache);

    // If we don't want any tokens, just peek from cache
    if want == 0 {
      return unsafe { self.cache.peek(buf) };
    }

    // Then, lex more tokens if needed
    let mut lexer = self.lexer();
    while want > 0 {
      if let Some(lexed) = Lexed::lex_spanned(&mut lexer) {
        let (span, lexed) = lexed.into_components();
        let cached = CachedToken::new(Spanned::new(span, lexed), lexer.extras.clone());

        // If it can be cached, cache it, the do not write to buffer
        // as the outer peek will write to buffer from cache
        match self.cache.push_back(cached) {
          Ok(_) => {
            in_cache += 1;
          }
          Err(ct) => {
            buf[buf_len - want].write(MaybeRef::Owned(ct));
          },
        }
        want -= 1;
      } else {
        break;
      }
    }

    let output = unsafe { self.cache.peek(&mut buf[..in_cache]) };
    debug_assert!(output.len() == in_cache, "Cache peek returned unexpected number of tokens");
    output
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

  /// Jumps to the given checkpoint.
  #[doc(alias = "rewinds")]
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn go(&mut self, checkpoint: Checkpoint<'a, '_, T>) {
    self.cache.rewind(&checkpoint);
    self.set_cursor(checkpoint.cursor().cursor);
    self.state = checkpoint.state;
  }

  /// Advances the cursor and returns the next valid token, emit non-fatal errors, fatal errors are returned and stop the process.
  pub fn next_valid_with<E>(
    &mut self,
    mut emitter: E,
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
          emitter.emit_token_error(Spanned::new(span, e))?;
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
          emitter.emit_token_error(Spanned::new(span, e))?;
          continue;
        }
      }
    }

    Ok(None)
  }

  // /// Advances the cursor and returns the next valid token, emit non-fatal errors, fatal errors are returned and stop the process.
  // pub fn next_valid<E>(&mut self, emitter: E) -> Result<Option<Spanned<T>>, E::Error>
  // where
  //   E: Emitter<'a, T>,
  //   E::Error: From<<T::Logos as Logos<'a>>::Error>,
  // {
  //   self.next_valid_with(emitter)
  // }

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

  /// Emits a non-fatal token error, if this error is a fatal error, then returns the error back.
  fn emit_token_error(&mut self, err: Spanned<<T::Logos as Logos<'a>>::Error>) -> Result<(), Self::Error>;

  /// Emits a non-fatal error, if this error is a fatal error, then returns the error back.
  fn emit_error(&mut self, err: Spanned<Self::Error>) -> Result<(), Self::Error>;
}

impl<'a, T, U> Emitter<'a, T> for &mut U
where
  T: Token<'a>,
  U: Emitter<'a, T>,
{
  type Error = U::Error;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_error(&mut self, err: Spanned<Self::Error>) -> Result<(), Self::Error> {
    (**self).emit_error(err)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_token_error(&mut self, err: Spanned<<T::Logos as Logos<'a>>::Error>) -> Result<(), Self::Error> {
    (**self).emit_token_error(err)
  }
}

/// A cached token with its associated extras.
pub struct CachedToken<'a, T: Token<'a>> {
  token: Spanned<Lexed<'a, T>>,
  state: <T::Logos as Logos<'a>>::Extras,
}

impl<'a, T: Token<'a>> Clone for CachedToken<'a, T>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      token: self.token.clone(),
      state: self.state.clone(),
    }
  }
}

impl<'a, T: Token<'a>> CachedToken<'a, T> {
  /// Creates a new cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(token: Spanned<Lexed<'a, T>>, state: <T::Logos as Logos<'a>>::Extras) -> Self {
    Self { token, state, }
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

  /// Returns a reference to the state.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn state(&self) -> &<T::Logos as Logos<'a>>::Extras {
    &self.state
  }

  /// Consumes the cached token and returns the extras.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Spanned<Lexed<'a, T>>, <T::Logos as Logos<'a>>::Extras) {
    (self.token, self.state)
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

  /// Returns the remaining capacity of the cache.
  fn remaining(&self) -> usize;

  /// Rewinds to the given checkpoint.
  fn rewind(&mut self, checkpoint: &Checkpoint<'a, '_, T>);

  /// Caches one token.
  ///
  /// If the cache is full, returns the token back, otherwise returns a reference to the token.
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T>,
  ) -> Result<&CachedToken<'a, T>, CachedToken<'a, T>>;

  /// Pops one cached token.
  #[allow(clippy::type_complexity)]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T>>;

  /// Pops one cached token from back.
  #[allow(clippy::type_complexity)]
  fn pop_back(&mut self) -> Option<CachedToken<'a, T>>;

  /// Clears the cache.
  fn clear(&mut self);

  /// Pops one cached token.
  #[allow(clippy::type_complexity)]
  fn pop_front_if<F>(&mut self, mut predicate: F) -> Option<CachedToken<'a, T>>
  where
    F: FnMut(&CachedToken<'a, T>) -> bool,
  {
    if let Some(peeked) = self.first() {
      if predicate(peeked) {
        return self.pop_front();
      }
    }
    None
  }

  /// Peeks one cached token without removing it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn peek_one<'c>(&self) -> Option<MaybeRef<'_, CachedToken<'a, T>>>
  where
    'a: 'c,
  {
    let mut buf: [MaybeUninit<MaybeRef<'_, CachedToken<'a, T>>>; 1] = [MaybeUninit::uninit()];
    let feed = unsafe { self.peek(&mut buf) };
    if feed.is_empty() {
      return None;
    }

    // SAFETY: We just checked that the buffer is not empty, so the first element is initialized.
    buf.into_iter().next().map(|m| unsafe { m.assume_init() })
  }

  /// Try to peeks cached tokens without removing them.
  ///
  /// The provided buffer will be filled with the peeked tokens, and the returned slice will contain only the initialized tokens.
  /// 
  /// # Safety
  /// - The implementor must ensure that the returned slice only contains initialized tokens.
  /// - The implementor must ensure all cached tokens should be filled into the provided buffer if the buffer is large enough.
  #[allow(clippy::mut_from_ref)]
  unsafe fn peek(
    &self,
    buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T>>>],
  ) -> &mut [MaybeRef<'_, CachedToken<'a, T>>];

  /// Pushes a batch of tokens into the cache.
  ///
  /// # Note
  ///
  /// If the cache is full, returns an iterator over the tokens that not be cached.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_many<'p>(
    &'p mut self,
    toks: impl Iterator<Item = CachedToken<'a, T>> + 'p,
  ) -> impl Iterator<Item = CachedToken<'a, T>> + 'p
  {
    toks.filter_map(move |tok| self.push_back(tok).err())
  }

  /// Returns the first cached token.
  fn first(&self) -> Option<&CachedToken<'a, T>>;

  /// Returns the last cached token.
  fn last(&self) -> Option<&CachedToken<'a, T>>;

  /// Returns the span of the cached tokens, from the start of the first to the end of the last.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span(&self) -> Option<Span> {
    match (self.first(), self.last()) {
      (Some(first), Some(last)) => Some(Span::new(first.token().span().start(), last.token().span().end())),
      _ => None,
    }
  }

  /// Returns the span of the first cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_first(&self) -> Option<Span> {
    self.first().map(|t| t.token().span())
  }

  /// Returns the span of the last cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_last(&self) -> Option<Span> {
    self.last().map(|t| t.token().span())
  }
}

/// A block hole will eat all the stuff.
#[derive(Debug, Clone, Copy, Default)]
pub struct BlackHole;

impl<'a, T> Cache<'a, T> for BlackHole
where
  T: Token<'a>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    0
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining(&self) -> usize {
    0
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn rewind(&mut self, _: &Checkpoint<'a, '_, T>) {}

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T>,
  ) -> Result<&CachedToken<'a, T>, CachedToken<'a, T>> {
    Err(tok)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_back(&mut self) -> Option<CachedToken<'a, T>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clear(&mut self) {}

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn peek(
    &self,
    buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T>>>],
  ) -> &mut [MaybeRef<'_, CachedToken<'a, T>>] {
    // SAFETY: We never initialize any element in the buffer, so the returned slice is always empty.
    unsafe {
      core::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut MaybeRef<'_, CachedToken<'a, T>>, 0)
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn first(&self) -> Option<&CachedToken<'a, T>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn last(&self) -> Option<&CachedToken<'a, T>> {
    None
  }
}

impl<'a, T> Emitter<'a, T> for BlackHole
where
  T: Token<'a>,
{
  type Error = core::convert::Infallible;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_token_error(&mut self, _err: Spanned<<T::Logos as Logos<'a>>::Error>) -> Result<(), Self::Error> {
    Ok(())
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_error(&mut self, _err: Spanned<Self::Error>) -> Result<(), Self::Error> {
    Ok(())
  }
}

