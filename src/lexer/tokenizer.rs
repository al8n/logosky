use core::{marker::PhantomData, mem::MaybeUninit, ops::Range};

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
pub struct Tokenizer<'a, T: Token<'a>, L: Lexer<'a, T>, C = ()> {
  pub(crate) input: &'a T::Source,
  pub(crate) state: L::State,
  pub(crate) cursor: usize,
  pub(crate) cache: C,
}

impl<'a, T, L, C> Clone for Tokenizer<'a, T, L, C>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
  L::State: Clone,
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

impl<'a, T, L, C> core::fmt::Debug for Tokenizer<'a, T, L, C>
where
  T: Token<'a>,
  T::Source: core::fmt::Debug,
  L: Lexer<'a, T>,
  L::State: core::fmt::Debug,
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

impl<'a, T, L> Tokenizer<'a, T, L>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
  L::State: Default,
{
  /// Creates a new lexer from the given input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(input: &'a T::Source) -> Self {
    Self::with_state(input, L::State::default())
  }
}

impl<'a, T, L> Tokenizer<'a, T, L>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
{
  /// Creates a new lexer from the given input and state.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_state(input: &'a T::Source, state: L::State) -> Self {
    Self {
      input,
      state,
      cursor: 0,
      cache: (),
    }
  }
}

impl<'a, T, L, C> Tokenizer<'a, T, L, C>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
{
  /// Returns a reference to the tokenizer's cache.
  ///
  /// The cache stores peeked tokens that have been lexed but not yet consumed.
  /// This can be useful for inspecting the cache state or implementing custom
  /// lookahead logic.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn cache(&self) -> &C {
    &self.cache
  }

  /// Returns a reference to the underlying input source.
  ///
  /// This allows access to the raw source being tokenized, which is typically
  /// a `&str` or `&[u8]` depending on your Logos token definition.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn input(&self) -> &T::Source {
    self.input
  }

  /// Returns a reference to the current lexer state (extras)
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn state(&self) -> &L::State {
    &self.state
  }

  /// Manually sets the lexer state (for context-sensitive lexing)
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn set_state(&mut self, state: L::State) {
    self.state = state;
  }

  /// Returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn iter(&mut self) -> iter::Iter<'a, '_, T, L, C> {
    iter::Iter::new(self)
  }

  /// Consumes the lexer and returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn into_iter(self) -> iter::IntoIter<'a, T, L, C> {
    iter::IntoIter::new(self)
  }

  /// Creates a Logos lexer positioned at the end of the cache or current cursor.
  ///
  /// This internal method constructs a fresh Logos lexer with the current state and
  /// positions it to continue lexing from where the cache ends (or from the cursor
  /// if the cache is empty).
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn lexer(&self) -> L
  where
    L::State: Clone,
    C: Cache<'a, T, L>,
  {
    let mut lexer = L::with_state(self.input, self.state.clone());
    lexer.bump(
      self
        .cache
        .span_last()
        .map(|s| s.end())
        .unwrap_or(self.cursor),
    );
    lexer
  }

  /// Sets the cursor to the specified position, clamped to the input length.
  ///
  /// This ensures the cursor never exceeds the bounds of the input source.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn set_cursor(&mut self, new: usize) {
    self.cursor = new.min(self.input.len());
  }

  /// Sets the cursor to the latest position between the new value and the cache start.
  ///
  /// This method ensures the cursor is positioned at or after the first cached token
  /// (if any), preventing the cursor from moving backwards past cached tokens.
  /// The cursor is also clamped to the input length.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn set_cursor_after_consume(&mut self, new: usize)
  where
    C: Cache<'a, T, L>,
  {
    self.cursor = new
      .max(self.cache.span_first().map(|s| s.start()).unwrap_or(new))
      .min(self.input.len());
    debug_assert!(
      self.cursor <= self.input.len(),
      "Cursor exceeded input bounds"
    );
  }
}

impl<'a, T, L, C> Tokenizer<'a, T, L, C>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
  L::State: Clone,
  C: Cache<'a, T, L>,
{
  // /// Try parsing, returns `None` on failure (no error propagation)
  // pub fn attempt<F, R>(&mut self, f: F) -> Option<R>
  // where
  //   F: FnOnce(&mut Self) -> Option<R>,
  // {
  //   let cur = self.cursor().cursor;
  //   let state = self.state.clone();

  //   match f(self) {
  //     Some(result) => Some(result),
  //     None => {
  //       let ckp = Checkpoint::new(Cursor::new(cur, self), state);
  //       self.go(ckp);
  //       None
  //     }
  //   }
  // }

  /// Consumes a token if it matches the predicate, returns `None` otherwise (no cursor advance on failure)
  pub fn accept<F>(&mut self, pred: F) -> Option<Spanned<T>>
  where
    F: FnOnce(&T) -> bool,
  {
    if let Some(peeked) = self.cache.first() {
      match peeked.token().data() {
        Lexed::Token(tk) if pred(tk) => {
          let tok = self.cache.pop_front().unwrap();
          let (spanned_lexed, extras) = tok.into_components();
          let (span, lexed) = spanned_lexed.into_components();
          self.set_cursor_after_consume(span.end());
          self.state = extras;
          return Some(Spanned::new(span, lexed.unwrap_token()));
        }
        _ => return None,
      }
    }

    let mut lexer = self.lexer();
    if let Some(lexed) = Lexed::<T>::lex_spanned(&mut lexer) {
      let (span, lexed) = lexed.into_components();

      if let Lexed::Token(tk) = &lexed {
        if pred(tk) {
          self.set_cursor_after_consume(lexer.span().end());
          self.state = lexer.into_state();
          return Some(Spanned::new(span, lexed.unwrap_token()));
        }
      }

      // cache the token as it was peeked
      let ct = CachedToken::new(Spanned::new(span, lexed), lexer.into_state());
      match self.cache.push_back(ct) {
        Ok(_) => {}
        Err(_) => {
          // cache full, do nothing
        }
      }
    }

    None
  }

  /// Consumes the next token if it matches the predicate, otherwise returns an error.
  pub fn expect<F, E>(
    &mut self,
    pred: F,
    error_fn: impl FnOnce(Lexed<'a, T>) -> E,
  ) -> Result<Option<Spanned<T>>, E>
  where
    F: FnOnce(&T) -> bool,
  {
    if let Some(peeked) = self.cache.first() {
      match peeked.token().data() {
        Lexed::Token(tk) if pred(tk) => {
          let tok = self.cache.pop_front().unwrap();
          let (spanned_lexed, extras) = tok.into_components();
          let (span, lexed) = spanned_lexed.into_components();
          self.set_cursor_after_consume(span.end());
          self.state = extras;
          return Ok(Some(Spanned::new(span, lexed.unwrap_token())));
        }
        _ => {
          let tok = self.cache.pop_front().unwrap();
          let (spanned_lexed, extras) = tok.into_components();
          let (span, lexed) = spanned_lexed.into_components();
          self.set_cursor_after_consume(span.end());
          self.state = extras;
          return Err(error_fn(lexed));
        }
      }
    }

    let mut lexer = self.lexer();

    if let Some(lexed) = Lexed::lex_spanned(&mut lexer) {
      let (span, lexed) = lexed.into_components();

      match &lexed {
        Lexed::Token(tk) if pred(tk) => {
          self.set_cursor_after_consume(lexer.span().end());
          self.state = lexer.into_state();
          return Ok(Some(Spanned::new(span, lexed.unwrap_token())));
        }
        _ => {
          self.set_cursor_after_consume(lexer.span().end());
          self.state = lexer.into_state();
          return Err(error_fn(lexed));
        }
      }
    }

    Ok(None)
  }

  /// Returns a slice of the input source from the given cursor to the current cursor of the tokenizer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn slice_since(
    &self,
    cursor: &Cursor<'a, '_, T, L, C>,
  ) -> Option<<T::Source as Source>::Slice<'a>> {
    let start = cursor.cursor;
    let end = self.cursor().cursor;
    self.input.slice(start..end)
  }

  /// Returns a slice of the input source from the given cursor to the end of the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn slice_from(
    &self,
    cursor: &Cursor<'a, '_, T, L, C>,
  ) -> Option<<T::Source as Source>::Slice<'a>> {
    let start = cursor.cursor;
    let end = self.input.len();
    self.input.slice(start..end)
  }

  /// Returns a slice of the input source from the current cursor of the tokenizer to the end of the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn slice(
    &self,
    range: Range<&Cursor<'a, '_, T, L, C>>,
  ) -> Option<<T::Source as Source>::Slice<'a>> {
    let start = range.start.cursor;
    let end = range.end.cursor;
    // SAFETY: The range is guaranteed to be within bounds as both cursors are within input length and comes from the same input.
    self.input.slice(start..end)
  }

  /// Returns a span from the given cursor to the current cursor of the tokenizer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span_since(&self, cursor: &Cursor<'a, '_, T, L, C>) -> Span {
    Span::new(cursor.cursor, self.cursor().cursor)
  }

  /// Returns a span from the given cursor to the end of the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span_from(&self, cursor: &Cursor<'a, '_, T, L, C>) -> Span {
    Span::new(cursor.cursor, self.input.len())
  }

  /// Returns a span from the current cursor of the tokenizer to the end of the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span(&self, range: Range<&Cursor<'a, '_, T, L, C>>) -> Span {
    Span::new(range.start.cursor, range.end.cursor)
  }

  /// Consumes one token from the peeked tokens and returns the consumed token if any, the cursor is advanced.
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[allow(clippy::type_complexity)]
  pub fn consume_one(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    let tok = self.cache.pop_front()?;
    let (tok, extras): (Spanned<Lexed<'a, T>>, _) = tok.into_components();
    self.set_cursor_after_consume(tok.span().end());
    self.state = extras;
    Some(tok)
  }

  /// Consumes tokens from cache until the predicate returns `true`, the cursor is advanced to the end of the last consumed token.
  ///
  /// Returns the last consumed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_until<F>(&mut self, mut f: F) -> Option<Spanned<Lexed<'a, T>>>
  where
    F: FnMut(&CachedToken<'a, T, L>) -> bool,
  {
    let mut last = None;
    // pop from cache if not matching
    while let Some(tok) = self.cache.pop_front_if(|t| !f(t)) {
      self.set_cursor_after_consume(tok.token().span().end());
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
    F: FnMut(&CachedToken<'a, T, L>) -> bool,
  {
    self.consume_until(|t| !f(t))
  }

  /// Consumes all cached tokens, the cursor is advanced to the end of the last cached token.
  ///
  /// Returns the last consumed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn consume_cached(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    let last = self.cache.pop_back()?;
    self.cache.clear();
    let (tok, extras): (Spanned<Lexed<'a, T>>, _) = last.into_components();
    self.set_cursor_after_consume(tok.span().end());
    self.state = extras;
    Some(tok)
  }

  /// Skips one token, advancing the cursor.
  ///
  /// If there's a token in the cache, it pops and discards it. Otherwise,
  /// it lexes the next token and discards it.
  ///
  /// Returns `true` if a token was skipped, `false` if the end of input was reached.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_one(&mut self) -> bool {
    if let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, _lexed) = spanned_lexed.into_components();
      self.set_cursor_after_consume(span.end());
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
  pub fn skip_until<F>(&mut self, mut pred: F) -> Option<MaybeRef<'_, CachedToken<'a, T, L>>>
  where
    F: FnMut(&Spanned<Lexed<'a, T>>) -> bool,
  {
    // pop from cache if not matching
    while let Some(tok) = self.cache.pop_front_if(|t| !pred(t.token())) {
      self.set_cursor_after_consume(tok.token().span().end());
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
            let ct = CachedToken::new(lexed, lexer.state().clone());
            self.set_cursor_after_consume(end);
            self.state = state;

            return match self.cache.push_back(ct) {
              Ok(tok) => Some(MaybeRef::Ref(tok)),
              Err(ct) => Some(MaybeRef::Owned(ct)),
            };
          }

          end = lexer.span().end();
          state = lexer.state().clone();
        }

        // No matched token found, we just update the cursor and state
        self.set_cursor_after_consume(lexer.span().end());
        self.state = lexer.into_state();

        None
      }
    }
  }

  /// Skips tokens while the predicate returns `true`.
  ///
  /// Returns the first token that does not match the predicate, but without consuming it.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_while<F>(&mut self, mut pred: F) -> Option<MaybeRef<'_, CachedToken<'a, T, L>>>
  where
    F: FnMut(&Spanned<Lexed<'a, T>>) -> bool,
  {
    self.skip_until(|t| !pred(t))
  }

  /// Skips error tokens until a valid token is found or the end of input is reached.
  ///
  /// Returns the first valid token found, but without consuming it.
  pub fn skip_until_valid(&mut self) -> Option<MaybeRef<'_, CachedToken<'a, T, L>>> {
    self.skip_until(|t| matches!(t.data, Lexed::Token(_)))
  }

  /// Skips tokens until the predicate returns `true`, emitting errors using the provided emitter.
  ///
  /// This method advances through the token stream, skipping tokens until it finds one that
  /// matches the predicate. Any lexer errors encountered are emitted via the provided emitter.
  /// If a fatal error occurs during emission, the method returns immediately with that error.
  ///
  /// Returns the first token that matches the predicate, but without consuming it.
  /// If no matching token is found, returns `None`.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn skip_until_with_emitter<F, E>(
    &mut self,
    mut pred: F,
    mut emitter: E,
  ) -> Result<Option<MaybeRef<'_, CachedToken<'a, T, L>>>, E::Error>
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
      self.set_cursor_after_consume(span.end());
      self.state = tok.state;

      // Note: cursor/state are updated before emission. If emission fails,
      // the error token has still been consumed (no backtracking here).
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
            Lexed::Error(err) => match emitter.emit_token_error(Spanned::new(span, err)) {
              Ok(_) => {
                end = lexer.span().end();
                state = lexer.state().clone();
              }
              Err(e) => {
                self.set_cursor_after_consume(lexer.span().end());
                self.state = lexer.into_state();
                return Err(e);
              }
            },
            Lexed::Token(tok) => {
              let tok = Spanned::new(span, tok);
              // if the token matches, we cache it and return it
              if pred(tok.as_ref(), &mut emitter) {
                let ct = CachedToken::new(tok.map_data(Lexed::Token), lexer.into_state());
                self.set_cursor_after_consume(end);
                self.state = state;
                return Ok(match self.cache.push_back(ct) {
                  Ok(tok) => Some(MaybeRef::Ref(tok)),
                  Err(ct) => Some(MaybeRef::Owned(ct)),
                });
              }

              end = lexer.span().end();
              state = lexer.state().clone();
            }
          }
        }

        // No matched token found, we just update the cursor and state
        self.set_cursor_after_consume(lexer.span().end());
        self.state = lexer.into_state();

        Ok(None)
      }
    }
  }

  /// Peeks the next token without advancing the cursor.
  #[inline]
  pub fn peek_one(&mut self) -> Option<MaybeRef<'_, CachedToken<'a, T, L>>> {
    let mut buf: [MaybeUninit<MaybeRef<'_, CachedToken<'a, T, L>>>; 1] = [MaybeUninit::uninit()];
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
  pub fn peek(
    &mut self,
    buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T, L>>>],
  ) -> &mut [MaybeRef<'_, CachedToken<'a, T, L>>] {
    let buf_len = buf.len();
    let mut in_cache = self.cache.len();
    let mut want = buf_len.saturating_sub(in_cache);

    // If we already have enough tokens cached, just peek from cache
    if want == 0 {
      // SAFETY: Cache guarantees peek() returns only initialized tokens up to cache.len()
      return unsafe { self.cache.peek(buf) };
    }

    // Otherwise, lex additional tokens to fill the request
    let mut lexer = self.lexer();
    while want > 0 {
      if let Some(lexed) = Lexed::lex_spanned(&mut lexer) {
        let (span, lexed) = lexed.into_components();
        let cached = CachedToken::new(Spanned::new(span, lexed), lexer.state().clone());

        // Try to cache the token; if cache is full, write directly to output buffer
        match self.cache.push_back(cached) {
          Ok(_) => {
            in_cache += 1;
          }
          Err(ct) => {
            // Cache full: write overflow tokens directly to buffer
            // Position: buf[buf_len - want] is the next unfilled slot
            buf[buf_len - want].write(MaybeRef::Owned(ct));
          }
        }
        want -= 1;
      } else {
        break;
      }
    }

    // Fill buffer from cache (this covers both cached tokens and any we just added)
    // SAFETY: Cache.peek() returns slice of initialized tokens, guaranteed by trait contract
    let output = unsafe { self.cache.peek(&mut buf[..in_cache]) };
    debug_assert!(
      output.len() == in_cache,
      "Cache peek returned unexpected number of tokens"
    );
    output
  }

  /// Saves the current state of the tokenizer as a checkpoint.
  ///
  /// This creates a snapshot of the current position and lexer state, which can
  /// later be restored using [`go`](Self::go). Checkpoints are essential for
  /// implementing backtracking in parsers.
  ///
  /// # Example
  ///
  /// ```ignore
  /// let checkpoint = tokenizer.save();
  /// // Try parsing something...
  /// if parsing_failed {
  ///     tokenizer.go(checkpoint); // Restore state
  /// }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn save(&self) -> Checkpoint<'a, '_, T, L, C> {
    Checkpoint::new(self.cursor(), self.state.clone())
  }

  /// Returns the current cursor position of the tokenizer.
  ///
  /// The cursor represents the byte offset in the input where the tokenizer will
  /// continue lexing. If there are cached tokens, the cursor points to the start
  /// of the first cached token; otherwise, it points to the current position.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn cursor(&self) -> Cursor<'a, '_, T, L, C> {
    Cursor::new(
      self
        .cache
        .span_first()
        .map(|s| s.start())
        .unwrap_or(self.cursor),
      self,
    )
  }

  /// Restores the tokenizer state to a previously saved checkpoint.
  ///
  /// This rewinds the cache, resets the cursor position, and restores the lexer
  /// state, effectively undoing all operations since the checkpoint was created.
  /// This is commonly used for parser backtracking.
  #[doc(alias = "rewinds")]
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn go(&mut self, checkpoint: Checkpoint<'a, '_, T, L, C>) {
    self.cache.rewind(&checkpoint);
    self.set_cursor(checkpoint.cursor().cursor);
    self.state = checkpoint.state;
  }

  /// Advances the cursor and returns the next valid token, emitting errors via the provided emitter.
  ///
  /// This method skips over lexer errors, emitting them through the provided emitter.
  /// Non-fatal errors are emitted and the method continues to the next token. If a
  /// fatal error occurs during emission, it's returned and processing stops.
  ///
  /// Returns `Ok(Some(token))` for valid tokens, `Ok(None)` at end of input, or
  /// `Err(error)` if a fatal error occurred.
  pub fn next_valid_with<E>(&mut self, mut emitter: E) -> Result<Option<Spanned<T>>, E::Error>
  where
    E: Emitter<'a, T>,
  {
    // First, consume from cache if available
    while let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, lexed) = spanned_lexed.into_components();
      self.set_cursor_after_consume(span.end());
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
      self.set_cursor_after_consume(lexer.span().end());
      self.state = lexer.state().clone();

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

  /// Advances the cursor and returns the next token (valid or error).
  ///
  /// Unlike [`next_valid_with`](Self::next_valid_with), this method returns both
  /// valid tokens and lexer errors wrapped in [`Lexed`]. The cursor advances
  /// regardless of whether a valid token or error is returned.
  ///
  /// Returns `Some(Spanned<Lexed>)` with either a token or error, or `None` at
  /// end of input.
  #[allow(clippy::should_implement_trait)]
  pub fn next(&mut self) -> Option<Spanned<Lexed<'a, T>>> {
    if let Some(cached_token) = self.cache.pop_front() {
      let (spanned_lexed, extras) = cached_token.into_components();
      let (span, lexed) = spanned_lexed.into_components();
      self.set_cursor_after_consume(span.end());
      self.state = extras;
      return Some(Spanned::new(span, lexed));
    }

    let mut lexer = self.lexer();
    Lexed::lex_spanned(&mut lexer).inspect(|_| {
      self.set_cursor_after_consume(lexer.span().end());
      self.state = lexer.state().clone();
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

/// A checkpoint that captures the tokenizer's state for backtracking.
///
/// A `Checkpoint` stores a snapshot of the tokenizer's position and lexer state
/// at a specific point in time. This allows you to save the current state using
/// [`Tokenizer::save`] and later restore it using [`Tokenizer::go`], enabling
/// efficient backtracking in parsers.
///
/// Checkpoints include:
/// - The cursor position (byte offset in the input)
/// - The lexer's extras state (for stateful lexers)
/// - Cache state (implicitly through the cursor)
///
/// # Example
///
/// ```ignore
/// let checkpoint = tokenizer.save();
/// // Try parsing something that might fail...
/// if should_backtrack {
///     tokenizer.go(checkpoint); // Restore to saved state
/// }
/// ```
pub struct Checkpoint<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> {
  cursor: Cursor<'a, 's, T, L, C>,
  state: L::State,
  _m: PhantomData<fn(&'s ()) -> &'s ()>,
}

impl<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> Checkpoint<'a, 's, T, L, C> {
  /// Creates a new checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(cursor: Cursor<'a, 's, T, L, C>, state: L::State) -> Self {
    Self {
      cursor,
      state,
      _m: PhantomData,
    }
  }

  /// Returns the cursor of the checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn cursor(&self) -> Cursor<'a, 's, T, L, C> {
    self.cursor
  }

  /// Returns the state of the checkpoint.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn state(&self) -> &L::State {
    &self.state
  }
}

/// A cursor representing a position in the input source.
///
/// `Cursor` is a lightweight type that wraps a byte offset into the tokenizer's
/// input source. It's used by [`Checkpoint`] to track positions and is returned
/// by [`Tokenizer::cursor`] to query the current position.
///
/// The cursor position represents:
/// - The byte offset in the input where the tokenizer will continue lexing
/// - If there are cached tokens, it points to the start of the first cached token
/// - Otherwise, it points to the position where the next token will be lexed from
pub struct Cursor<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> {
  cursor: usize,
  _input: &'s Tokenizer<'a, T, L, C>,
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> core::fmt::Debug for Cursor<'a, '_, T, L, C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "Cursor({})", self.cursor)
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> Clone for Cursor<'a, '_, T, L, C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> Copy for Cursor<'a, '_, T, L, C> {}

impl<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> Cursor<'a, 's, T, L, C> {
  /// Creates a new cursor.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(cursor: usize, tkn: &'s Tokenizer<'a, T, L, C>) -> Self {
    Self {
      cursor,
      _input: tkn,
    }
  }

  /// Returns the byte offset position in the input source.
  ///
  /// This is the absolute position (in bytes) where the tokenizer is currently
  /// positioned or where it will resume lexing.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn position(&self) -> usize {
    self.cursor
  }
}

/// A trait for handling and emitting errors during tokenization and parsing.
///
/// `Emitter` provides a unified interface for error handling in the tokenization pipeline.
/// Implementations can decide whether errors are fatal (stop processing) or non-fatal
/// (logged and processing continues). This is particularly useful when you want to collect
/// multiple errors before stopping, or when implementing error recovery.
///
/// # Error Handling Strategy
///
/// The emitter uses a `Result`-based approach where:
/// - `Ok(())` means the error was handled as non-fatal and processing should continue
/// - `Err(error)` means the error is fatal and processing should stop immediately
///
/// # Use Cases
///
/// - **Error Collection**: Accumulate multiple errors before reporting them all at once
/// - **Error Recovery**: Log errors but continue parsing to find more issues
/// - **Fail-Fast**: Stop on the first error by always returning `Err`
/// - **Filtering**: Only treat certain error types as fatal
///
/// # Example
///
/// ```ignore
/// struct MyEmitter {
///     errors: Vec<String>,
///     max_errors: usize,
/// }
///
/// impl<'a, T: Token<'a>> Emitter<'a, T> for MyEmitter {
///     type Error = String;
///
///     fn emit_token_error(&mut self, err: Spanned<...>) -> Result<(), Self::Error> {
///         self.errors.push(format!("Lexer error at {:?}", err.span));
///         if self.errors.len() >= self.max_errors {
///             Err("Too many errors".to_string())
///         } else {
///             Ok(())
///         }
///     }
///
///     fn emit_error(&mut self, err: Spanned<Self::Error>) -> Result<(), Self::Error> {
///         self.errors.push(err.data);
///         if self.errors.len() >= self.max_errors {
///             Err("Too many errors".to_string())
///         } else {
///             Ok(())
///         }
///     }
/// }
/// ```
pub trait Emitter<'a, T: Token<'a>> {
  /// The error type that this emitter produces.
  ///
  /// This is the type returned when a fatal error occurs (via `Err(Self::Error)`).
  /// It can be any type that represents your application's error model.
  type Error;

  /// Emits a lexer error from the underlying Logos tokenizer.
  ///
  /// This method is called when Logos encounters an error during lexing (e.g.,
  /// invalid input that doesn't match any token pattern). The implementation
  /// decides whether to treat it as fatal or non-fatal.
  ///
  /// # Parameters
  ///
  /// - `err`: The lexer error wrapped with its source span
  ///
  /// # Returns
  ///
  /// - `Ok(())` if the error should be treated as non-fatal (processing continues)
  /// - `Err(Self::Error)` if the error is fatal (processing stops immediately)
  fn emit_token_error(&mut self, err: Spanned<T::Error>) -> Result<(), Self::Error>;

  /// Emits a custom error from the application or parser.
  ///
  /// This method is called for application-level errors (not lexer errors).
  /// Like `emit_token_error`, the implementation decides whether the error
  /// is fatal or should be logged and processing continued.
  ///
  /// # Parameters
  ///
  /// - `err`: The application error wrapped with its source span
  ///
  /// # Returns
  ///
  /// - `Ok(())` if the error should be treated as non-fatal (processing continues)
  /// - `Err(Self::Error)` if the error is fatal (processing stops immediately)
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
  fn emit_token_error(&mut self, err: Spanned<T::Error>) -> Result<(), Self::Error> {
    (**self).emit_token_error(err)
  }
}

/// A cached token with its associated extras.
pub struct CachedToken<'a, T: Token<'a>, L: Lexer<'a, T>> {
  token: Spanned<Lexed<'a, T>>,
  state: L::State,
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>> Clone for CachedToken<'a, T, L>
where
  L::State: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      token: self.token.clone(),
      state: self.state.clone(),
    }
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>> CachedToken<'a, T, L> {
  /// Creates a new cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(token: Spanned<Lexed<'a, T>>, state: L::State) -> Self {
    Self { token, state }
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
  pub const fn state(&self) -> &L::State {
    &self.state
  }

  /// Consumes the cached token and returns the extras.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Spanned<Lexed<'a, T>>, L::State) {
    (self.token, self.state)
  }
}

/// A trait for caching lookahead tokens in the tokenizer.
///
/// `Cache` provides a buffer for tokens that have been lexed but not yet consumed,
/// enabling efficient lookahead and backtracking operations. The cache acts as a
/// queue (FIFO - First In, First Out) between the lexer and the parser.
///
/// # Purpose
///
/// The cache serves several critical functions:
/// - **Lookahead**: Allows peeking at future tokens without consuming them
/// - **Backtracking**: Supports parser backtracking via checkpoint/rewind operations
/// - **Efficiency**: Avoids re-lexing tokens that have already been processed
/// - **State Management**: Preserves lexer state (extras) alongside each token
///
/// # Design Patterns
///
/// Different implementations support different use cases:
/// - **Fixed-size arrays**: Bounded lookahead with known maximum (e.g., `[CachedToken; 4]`)
/// - **Dynamic buffers**: Unlimited lookahead using `Vec` or `VecDeque`
/// - **BlackHole**: No caching at all, for streaming-only scenarios without backtracking
///
/// Note: Tokens cannot be overwritten until explicitly consumed, as they must remain
/// available for backtracking operations. This means the cache can become full and
/// refuse new tokens if capacity is reached.
///
/// # Cache Operations
///
/// The cache supports standard queue operations:
/// - `push_back`: Add newly lexed tokens to the end (fails if cache is full)
/// - `pop_front`: Remove and return the oldest token
/// - `peek`: View tokens without removing them
/// - `rewind`: Restore to a previous state (for backtracking)
///
/// # Safety
///
/// The `peek` method is marked unsafe because it requires implementations to guarantee
/// that returned slices only contain properly initialized tokens. This is enforced by
/// the trait's contract.
///
/// # Example
///
/// ```ignore
/// // A simple fixed-size cache using a VecDeque-like structure
/// struct BoundedCache<'a, T: Token<'a>> {
///     tokens: VecDeque<CachedToken<'a, T>>,
///     capacity: usize,
/// }
///
/// impl<'a, T: Token<'a>> Cache<'a, T> for BoundedCache<'a, T> {
///     fn len(&self) -> usize {
///         self.tokens.len()
///     }
///
///     fn remaining(&self) -> usize {
///         self.capacity - self.tokens.len()
///     }
///
///     fn push_back(&mut self, tok: CachedToken<'a, T>) -> Result<&CachedToken<'a, T>, CachedToken<'a, T>> {
///         if self.tokens.len() < self.capacity {
///             self.tokens.push_back(tok);
///             Ok(self.tokens.back().unwrap())
///         } else {
///             Err(tok) // Cache full, cannot overwrite!
///         }
///     }
///     // ... other methods
/// }
/// ```
pub trait Cache<'a, T: Token<'a>, L: Lexer<'a, T>> {
  /// Returns `true` if the cache contains no tokens.
  ///
  /// This is a convenience method that checks if `len() == 0`.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the number of tokens currently stored in the cache.
  ///
  /// This count includes all cached tokens from front to back.
  fn len(&self) -> usize;

  /// Returns the number of additional tokens that can be cached.
  ///
  /// For unbounded caches (like `Vec`), this might return a large number.
  /// For fixed-size caches, this returns the number of free slots.
  /// For `BlackHole`, this always returns 0.
  fn remaining(&self) -> usize;

  /// Rewinds the cache to a previously saved checkpoint.
  ///
  /// This operation restores the cache state to match the checkpoint, typically
  /// by clearing any tokens that were added after the checkpoint was created.
  /// This is used for parser backtracking.
  fn rewind(&mut self, checkpoint: &Checkpoint<'a, '_, T, L, Self>)
  where
    Self: Sized;

  /// Attempts to add a token to the back of the cache.
  ///
  /// If successful, returns `Ok` with a reference to the cached token.
  /// If the cache is full, returns `Err` with the token so the caller can handle it
  /// (e.g., by processing it immediately without caching).
  ///
  /// # Example
  ///
  /// ```ignore
  /// match cache.push_back(token) {
  ///     Ok(cached_ref) => {
  ///         // Token was cached successfully
  ///     }
  ///     Err(token) => {
  ///         // Cache is full, handle token directly
  ///     }
  /// }
  /// ```
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T, L>,
  ) -> Result<&CachedToken<'a, T, L>, CachedToken<'a, T, L>>;

  /// Removes and returns the token at the front of the cache.
  ///
  /// Returns `None` if the cache is empty. This is the primary way to consume
  /// cached tokens.
  #[allow(clippy::type_complexity)]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T, L>>;

  /// Removes and returns the token at the back of the cache.
  ///
  /// Returns `None` if the cache is empty. This is less commonly used than
  /// `pop_front` but can be useful for certain cache management operations.
  #[allow(clippy::type_complexity)]
  fn pop_back(&mut self) -> Option<CachedToken<'a, T, L>>;

  /// Removes all tokens from the cache.
  ///
  /// After calling this method, `len()` returns 0 and `is_empty()` returns `true`.
  fn clear(&mut self);

  /// Conditionally removes and returns the front token if it matches a predicate.
  ///
  /// Peeks at the first token in the cache and checks if it satisfies the predicate.
  /// If it does, removes and returns it. Otherwise, returns `None` without modifying
  /// the cache.
  ///
  /// # Example
  ///
  /// ```ignore
  /// // Pop token only if it's a specific type
  /// if let Some(token) = cache.pop_front_if(|t| matches!(t.token().data, Lexed::Token(_))) {
  ///     // Process valid token
  /// }
  /// ```
  #[allow(clippy::type_complexity)]
  fn pop_front_if<F>(&mut self, predicate: F) -> Option<CachedToken<'a, T, L>>
  where
    F: FnOnce(&CachedToken<'a, T, L>) -> bool,
  {
    if let Some(peeked) = self.first() {
      if predicate(peeked) {
        return self.pop_front();
      }
    }
    None
  }

  /// Peeks at the first cached token without removing it.
  ///
  /// Returns `Some(MaybeRef)` with either a reference to the cached token or
  /// an owned token (if cache implementation requires). Returns `None` if the
  /// cache is empty.
  ///
  /// This is a convenience wrapper around `peek` for looking at just one token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn peek_one<'c>(&self) -> Option<MaybeRef<'_, CachedToken<'a, T, L>>>
  where
    'a: 'c,
  {
    let mut buf: [MaybeUninit<MaybeRef<'_, CachedToken<'a, T, L>>>; 1] = [MaybeUninit::uninit()];
    let feed = unsafe { self.peek(&mut buf) };
    if feed.is_empty() {
      return None;
    }

    // SAFETY: We just checked that the buffer is not empty, so the first element is initialized.
    buf.into_iter().next().map(|m| unsafe { m.assume_init() })
  }

  /// Peeks at multiple cached tokens without removing them.
  ///
  /// Fills the provided buffer with references to cached tokens (or owned tokens if
  /// necessary). The returned slice contains only the successfully initialized tokens,
  /// which may be fewer than requested if the cache doesn't have enough tokens.
  ///
  /// # Parameters
  ///
  /// - `buf`: A buffer of uninitialized `MaybeRef` entries to fill with peeked tokens
  ///
  /// # Returns
  ///
  /// A mutable slice containing initialized token references. The slice length indicates
  /// how many tokens were actually available.
  ///
  /// # Safety
  ///
  /// Implementations must guarantee that:
  /// - The returned slice contains only properly initialized tokens
  /// - All cached tokens are filled into the buffer if the buffer is large enough
  /// - The slice bounds are correct and don't include uninitialized memory
  ///
  /// Callers must ensure the returned slice is not used beyond its lifetime.
  #[allow(clippy::mut_from_ref)]
  unsafe fn peek(
    &self,
    buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T, L>>>],
  ) -> &mut [MaybeRef<'_, CachedToken<'a, T, L>>];

  /// Pushes multiple tokens into the cache at once.
  ///
  /// Attempts to cache all tokens from the iterator. If the cache becomes full,
  /// returns an iterator over the tokens that could not be cached.
  ///
  /// # Example
  ///
  /// ```ignore
  /// let overflow = cache.push_many(token_iter);
  /// for token in overflow {
  ///     // Handle tokens that didn't fit in cache
  /// }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_many<'p>(
    &'p mut self,
    toks: impl Iterator<Item = CachedToken<'a, T, L>> + 'p,
  ) -> impl Iterator<Item = CachedToken<'a, T, L>> + 'p {
    toks.filter_map(move |tok| self.push_back(tok).err())
  }

  /// Returns a reference to the first (oldest) cached token.
  ///
  /// Returns `None` if the cache is empty. This does not remove the token.
  fn first(&self) -> Option<&CachedToken<'a, T, L>>;

  /// Returns a reference to the last (newest) cached token.
  ///
  /// Returns `None` if the cache is empty. This does not remove the token.
  fn last(&self) -> Option<&CachedToken<'a, T, L>>;

  /// Returns the combined span covering all cached tokens.
  ///
  /// If the cache has tokens, returns a span from the start of the first token
  /// to the end of the last token. Returns `None` if the cache is empty.
  ///
  /// This is useful for error reporting or understanding the range of lookahead.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span(&self) -> Option<Span> {
    match (self.first(), self.last()) {
      (Some(first), Some(last)) => Some(Span::new(
        first.token().span().start(),
        last.token().span().end(),
      )),
      _ => None,
    }
  }

  /// Returns the span of the first cached token.
  ///
  /// Returns `None` if the cache is empty. This is often used to determine
  /// where the next consumed token will come from.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_first(&self) -> Option<Span> {
    self.first().map(|t| t.token().span())
  }

  /// Returns the span of the last cached token.
  ///
  /// Returns `None` if the cache is empty. This can be used to determine
  /// where the cache's lookahead ends.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span_last(&self) -> Option<Span> {
    self.last().map(|t| t.token().span())
  }
}

/// A black hole cache that discards all tokens.
///
/// `BlackHole` implements the [`Cache`] trait but doesn't actually store any tokens.
/// All tokens pushed to it are immediately discarded. This is useful when you want to
/// process tokens in a streaming fashion without maintaining a lookahead buffer.
#[derive(Debug, Clone, Copy, Default)]
pub struct BlackHole;

impl<'a, T, L> Cache<'a, T, L> for BlackHole
where
  T: Token<'a>,
  L: Lexer<'a, T>,
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
  fn rewind(&mut self, _: &Checkpoint<'a, '_, T, L, Self>) {}

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T, L>,
  ) -> Result<&CachedToken<'a, T, L>, CachedToken<'a, T, L>> {
    Err(tok)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T, L>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_back(&mut self) -> Option<CachedToken<'a, T, L>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clear(&mut self) {}

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn peek(
    &self,
    buf: &mut [MaybeUninit<MaybeRef<'_, CachedToken<'a, T, L>>>],
  ) -> &mut [MaybeRef<'_, CachedToken<'a, T, L>>] {
    // SAFETY: We never initialize any element in the buffer, so the returned slice is always empty.
    unsafe {
      core::slice::from_raw_parts_mut(
        buf.as_mut_ptr() as *mut MaybeRef<'_, CachedToken<'a, T, L>>,
        0,
      )
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn first(&self) -> Option<&CachedToken<'a, T, L>> {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn last(&self) -> Option<&CachedToken<'a, T, L>> {
    None
  }
}

impl<'a, T> Emitter<'a, T> for BlackHole
where
  T: Token<'a>,
{
  type Error = core::convert::Infallible;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_token_error(&mut self, _err: Spanned<T::Error>) -> Result<(), Self::Error> {
    Ok(())
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_error(&mut self, _err: Spanned<Self::Error>) -> Result<(), Self::Error> {
    Ok(())
  }
}
