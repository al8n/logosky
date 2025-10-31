use ::chumsky::{
  container::Container,
  extra::ParserExtra,
  input::{ExactSizeInput, Input, SliceInput, ValueInput},
  prelude::*,
};

use core::ops::Range;

use crate::{Lexed, LosslessToken, State, Tokenizer, utils};

use super::*;

impl<'a, T> Input<'a> for Tokenizer<'a, T>
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

impl<'a, T> ValueInput<'a> for Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
    unsafe { <Self as Input<'a>>::next_maybe(cache, cursor) }
  }
}

impl<'a, T> ExactSizeInput<'a> for Tokenizer<'a, T>
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

impl<'a, T> SliceInput<'a> for Tokenizer<'a, T>
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

/// TokenStream trait providing utilities for working with token streams.
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
/// use logosky::{TokenStream, TokenStream, LosslessToken};
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
pub trait TokenStream<'a, T: Token<'a>>:
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
  /// use logosky::TokenStream;
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
  /// This method is implemented as a call to [`collect_trivias()`](TokenStream::collect_trivias)
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
  /// use logosky::{TokenStream, utils::Spanned};
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
  /// skips over trivia tokens. This makes it equivalent to [`skip_trivias()`](TokenStream::skip_trivias)
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

impl<'a, T, I> TokenStream<'a, T> for I
where
  I: SliceInput<'a> + ValueInput<'a, Span = utils::Span, Token = Lexed<'a, T>>,
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: State,
{
}
