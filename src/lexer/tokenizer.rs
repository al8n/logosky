use chumsky::{
  container::Container,
  extra::ParserExtra,
  input::{ExactSizeInput, Input, SliceInput, ValueInput},
  prelude::*,
};

use core::ops::Range;

use crate::utils;

use super::*;

/// Iterators for [`TokenStream`]
pub mod iter;

/// A zero-copy token stream adapter that bridges Logos and Chumsky.
///
/// `TokenStream` is the core integration layer between [Logos](https://github.com/maciejhirsz/logos)
/// lexical analysis and [Chumsky](https://github.com/zesterer/chumsky) parser combinators.
/// It efficiently wraps a Logos token source and implements all necessary Chumsky input traits,
/// allowing you to use Chumsky parsers directly on Logos tokens.
///
/// # Zero-Copy Design
///
/// `TokenStream` doesn't allocate or copy tokens. Instead, it maintains a cursor position
/// and calls Logos on-demand as the parser consumes tokens. This makes it efficient for
/// large inputs and streaming scenarios.
///
/// # State Management
///
/// For stateful lexers (those with non-`()` `Extras`), `TokenStream` maintains the lexer
/// state and passes it through token-by-token. This allows for context-sensitive lexing
/// patterns.
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
/// use logosky::{Token, TokenStream, TokenExt};
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
/// let stream = MyToken::lexer(input); // Returns TokenStream<'_, MyToken>
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
/// let stream = TokenStream::with_state(input, initial_state);
/// ```
///
/// ## Cloning and Backtracking
///
/// TokenStream supports cloning (when the token type and extras are Clone/Copy),
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
pub struct TokenStream<'a, T: Token<'a>> {
  input: &'a <T::Logos as Logos<'a>>::Source,
  state: <T::Logos as Logos<'a>>::Extras,
  cursor: usize,
}

impl<'a, T> Clone for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      input: self.input,
      state: self.state.clone(),
      cursor: self.cursor,
    }
  }
}

impl<'a, T> Copy for TokenStream<'a, T>
where
  T: Token<'a> + Copy,
  <T::Logos as Logos<'a>>::Extras: Copy,
  <T::Logos as Logos<'a>>::Error: Copy,
{
}

impl<'a, T> core::fmt::Debug for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("TokenStream")
      .field("input", &self.input)
      .field("state", &self.state)
      .finish()
  }
}

impl<'a, T> TokenStream<'a, T>
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

impl<'a, T: Token<'a>> TokenStream<'a, T> {
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
    }
  }
}

impl<'a, T: Token<'a>> TokenStream<'a, T> {
  /// Returns a reference to the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn input(&self) -> &<T::Logos as Logos<'a>>::Source {
    self.input
  }

  /// Returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn iter(&mut self) -> iter::Iter<'a, '_, T> {
    iter::Iter::new(self)
  }

  /// Consumes the lexer and returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn into_iter(self) -> iter::IntoIter<'a, T> {
    iter::IntoIter::new(self)
  }
}

impl<'a, T> Input<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  type Span = utils::Span;

  type Token = Lexed<'a, T>;

  type MaybeToken = Lexed<'a, T>;

  type Cursor = usize;

  type Cache = Self;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn begin(self) -> (Self::Cursor, Self::Cache) {
    (0, self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn cursor_location(cursor: &Self::Cursor) -> usize {
    *cursor
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn next_maybe(
    this: &mut Self::Cache,
    cursor: &mut Self::Cursor,
  ) -> Option<Self::MaybeToken> {
    let mut lexer = logos::Lexer::<T::Logos>::with_extras(this.input, this.state);
    lexer.bump(*cursor);
    Lexed::lex(&mut lexer).inspect(|_| {
      *cursor = lexer.span().end;
      this.state = lexer.extras;
      this.cursor = *cursor;
    })
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn span(_: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
    utils::Span::new(*range.start, *range.end)
  }
}

impl<'a, T> ValueInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
    unsafe { <Self as Input<'a>>::next_maybe(cache, cursor) }
  }
}

impl<'a, T> ExactSizeInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn span_from(
    cache: &mut Self::Cache,
    range: core::ops::RangeFrom<&Self::Cursor>,
  ) -> Self::Span {
    utils::Span::new(*range.start, cache.input.len())
  }
}

impl<'a, T> SliceInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
  <<T::Logos as Logos<'a>>::Source as logos::Source>::Slice<'a>: Clone,
{
  type Slice = <<T::Logos as Logos<'a>>::Source as logos::Source>::Slice<'a>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn full_slice(cache: &mut Self::Cache) -> Self::Slice {
    unsafe { cache.input.slice_unchecked(0..cache.input.len()) }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn slice(cache: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Slice {
    unsafe {
      <<T::Logos as Logos<'a>>::Source as logos::Source>::slice_unchecked(
        cache.input,
        *range.start..*range.end,
      )
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn slice_from(
    cache: &mut Self::Cache,
    from: core::ops::RangeFrom<&Self::Cursor>,
  ) -> Self::Slice {
    unsafe {
      <<T::Logos as Logos<'a>>::Source as logos::Source>::slice_unchecked(
        cache.input,
        *from.start..cache.input.len(),
      )
    }
  }
}

/// Tokenizer trait providing utilities for working with token streams.
///
/// This trait is automatically implemented for any type that implements Chumsky's
/// [`SliceInput`] and [`ValueInput`] traits with the appropriate associated types.
/// It provides parser combinators for handling trivia tokens when working with
/// [`LosslessToken`] implementations.
///
/// # Trivia Handling
///
/// When implementing parsers for languages with trivia (whitespace, comments), you typically
/// have two approaches:
///
/// 1. **Skip trivia entirely** - Use [`skip_trivias()`](Self::skip_trivias) to ignore formatting
/// 2. **Preserve trivia** - Use [`collect_trivias()`](Self::collect_trivias) to capture formatting information
///
/// # Example: Building a Simple Parser with Trivia
///
/// ```rust,ignore
/// use chumsky::prelude::*;
/// use logosky::{TokenStream, Tokenizer, LosslessToken};
///
/// type MyStream<'a> = TokenStream<'a, MyToken>;
///
/// // Parser that skips leading trivia
/// fn identifier_parser<'a>() -> impl Parser<'a, MyStream<'a>, String, extra::Err<EmptyErr>> {
///     MyStream::skip_trivias()
///         .ignore_then(any().try_map(|tok, _| {
///             if let Lexed::Token(t) = tok {
///                 if matches!(t.kind(), TokenKind::Identifier) {
///                     return Ok(t.text().to_string());
///                 }
///             }
///             Err(EmptyErr::default())
///         }))
/// }
///
/// // Parser that preserves trivia for formatting
/// fn statement_with_trivia<'a>() -> impl Parser<'a, MyStream<'a>, Statement, extra::Err<EmptyErr>> {
///     MyStream::collect_trivias::<Vec<_>, _>()
///         .then(statement_parser())
///         .map(|(leading_trivia, stmt)| Statement {
///             leading_trivia,
///             node: stmt,
///         })
/// }
/// ```
pub trait Tokenizer<'a, T: Token<'a>>:
  SliceInput<'a> + ValueInput<'a, Span = utils::Span, Token = Lexed<'a, T>>
{
  /// Returns a parser that skips over trivia tokens.
  ///
  /// This parser consumes all consecutive trivia tokens (as identified by
  /// [`LosslessToken::is_trivia()`]) from the input stream and returns `()`.
  /// It stops when it encounters a non-trivia token or reaches the end of input.
  ///
  /// # Use Cases
  ///
  /// - **Simple parsers** that don't need to preserve formatting
  /// - **Semantic analysis** where comments and whitespace are irrelevant
  /// - **Performance-critical parsing** where you want to skip trivia without allocation
  ///
  /// # Type Parameters
  ///
  /// - `E`: The parser extra/error type (e.g., `extra::Err<EmptyErr>`)
  ///
  /// # Requirements
  ///
  /// - The token type `T` must implement [`LosslessToken`]
  ///
  /// # Example
  ///
  /// ```rust,ignore
  /// use chumsky::prelude::*;
  /// use logosky::Tokenizer;
  ///
  /// // Skip trivia before parsing a number
  /// let parser = MyTokenStream::skip_trivias()
  ///     .ignore_then(number_parser());
  ///
  /// // Parse multiple tokens with trivia in between
  /// let expr_parser = term_parser()
  ///     .then_ignore(MyTokenStream::skip_trivias())
  ///     .then(operator_parser())
  ///     .then_ignore(MyTokenStream::skip_trivias())
  ///     .then(term_parser());
  /// ```
  ///
  /// # Performance
  ///
  /// This method is implemented as a call to [`collect_trivias()`](Tokenizer::collect_trivias)
  /// with `()` as the container type, which means it doesn't allocate and simply
  /// consumes trivia tokens without storing them.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn skip_trivias<E>() -> impl Parser<'a, Self, (), E> + Clone
  where
    Self: Sized + 'a,
    E: ParserExtra<'a, Self>,
    T: LosslessToken<'a>,
  {
    Self::collect_trivias::<(), E>()
  }

  /// Returns a parser that collects trivia tokens into a container.
  ///
  /// This parser consumes consecutive trivia tokens (as identified by
  /// [`LosslessToken::is_trivia()`]) and collects them into a container of type `C`.
  /// It stops collecting when it encounters a non-trivia token or reaches the end of input.
  ///
  /// # Use Cases
  ///
  /// - **Code formatters** that need to preserve original whitespace and comments
  /// - **Linters** that analyze comment placement or formatting
  /// - **Language servers** that provide hover information for documentation comments
  /// - **Syntax highlighters** that need to colorize comments differently
  ///
  /// # Type Parameters
  ///
  /// - `C`: The container type for collected tokens (e.g., `Vec<Spanned<T>>`, or `()` to skip)
  /// - `E`: The parser extra/error type (e.g., `extra::Err<EmptyErr>`)
  ///
  /// # Requirements
  ///
  /// - The token type `T` must implement [`LosslessToken`]
  /// - The container type `C` must implement [`Container<Spanned<T>>`](chumsky::container::Container)
  ///
  /// # Example
  ///
  /// ```rust,ignore
  /// use chumsky::prelude::*;
  /// use logosky::{Tokenizer, utils::Spanned};
  ///
  /// // Collect trivia into a Vec
  /// let parser = MyTokenStream::collect_trivias::<Vec<Spanned<MyToken>>, _>()
  ///     .then(statement_parser())
  ///     .map(|(trivia, stmt)| {
  ///         // Process trivia: extract documentation, check formatting, etc.
  ///         Statement {
  ///             leading_trivia: trivia,
  ///             node: stmt,
  ///         }
  ///     });
  ///
  /// // Skip trivia without allocation by using () as container
  /// let skip_parser = MyTokenStream::collect_trivias::<(), _>()
  ///     .ignore_then(token_parser());
  /// ```
  ///
  /// # Behavior
  ///
  /// - **Empty input**: Returns an empty container successfully
  /// - **No trivia**: Returns an empty container and doesn't consume any tokens
  /// - **Consecutive trivia**: Collects all trivia tokens until a non-trivia token
  /// - **Span preservation**: Each collected token retains its original span information
  ///
  /// # Performance
  ///
  /// When using `()` as the container type, this method doesn't allocate and simply
  /// skips over trivia tokens. This makes it equivalent to [`skip_trivias()`](Tokenizer::skip_trivias)
  /// in terms of performance.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn collect_trivias<C, E>() -> impl Parser<'a, Self, C, E> + Clone
  where
    Self: Sized + 'a,
    C: Container<utils::Spanned<T>> + 'a,
    E: ParserExtra<'a, Self>,
    T: LosslessToken<'a>,
  {
    custom(|inp| {
      let mut container = C::default();

      loop {
        let tok: Option<Lexed<'a, T>> = inp.peek();
        match tok {
          Some(Lexed::Token(tok)) if tok.is_trivia() => {
            container.push(tok);
            inp.skip();
          }
          _ => break,
        }
      }
      Ok(container)
    })
  }
}

impl<'a, T, I> Tokenizer<'a, T> for I
where
  I: SliceInput<'a> + ValueInput<'a, Span = utils::Span, Token = Lexed<'a, T>>,
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: State,
{
}
