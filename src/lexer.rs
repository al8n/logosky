use core::ops::Range;

use chumsky::input::{ExactSizeInput, Input, SliceInput, ValueInput};

pub use error::*;
pub use source::Source;
pub use token::{Lexed, Logos, Token, TokenExt};

use crate::utils;

mod error;

/// The token related structures and traits
pub mod token;

/// The source related structures and traits
pub mod source;

/// Iterators for [`TokenStream`]
pub mod iter;

/// A trait for types that can be lexed from the input.
pub trait Lexable<I, Error> {
  /// Lexes `Self` from the given input.
  fn lex(input: I) -> Result<Self, Error>
  where
    Self: Sized;
}

/// The logos token stream adapter for chumsky's parsers
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
  #[inline(always)]
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
  #[inline]
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
  #[inline(always)]
  pub fn new(input: &'a <T::Logos as Logos<'a>>::Source) -> Self {
    Self::with_state(input, <T::Logos as Logos<'a>>::Extras::default())
  }
}

impl<'a, T: Token<'a>> TokenStream<'a, T> {
  /// Creates a new lexer from the given input and state.
  #[inline(always)]
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
  #[inline(always)]
  pub const fn input(&self) -> &<T::Logos as Logos<'a>>::Source {
    self.input
  }

  /// Returns an iterator over the tokens of the lexer.
  #[inline(always)]
  pub const fn iter(&mut self) -> iter::Iter<'a, '_, T> {
    iter::Iter::new(self)
  }

  /// Consumes the lexer and returns an iterator over the tokens of the lexer.
  #[inline(always)]
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

  #[inline(always)]
  fn begin(self) -> (Self::Cursor, Self::Cache) {
    (0, self)
  }

  #[inline(always)]
  fn cursor_location(cursor: &Self::Cursor) -> usize {
    *cursor
  }

  #[inline(always)]
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

  #[inline(always)]
  unsafe fn span(_: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
    utils::Span::new(*range.start, *range.end)
  }
}

impl<'a, T> ValueInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  #[inline(always)]
  unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
    unsafe { <Self as Input<'a>>::next_maybe(cache, cursor) }
  }
}

impl<'a, T> ExactSizeInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  #[inline(always)]
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

  #[inline(always)]
  fn full_slice(cache: &mut Self::Cache) -> Self::Slice {
    unsafe { cache.input.slice_unchecked(0..cache.input.len()) }
  }

  #[inline(always)]
  unsafe fn slice(cache: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Slice {
    unsafe {
      <<T::Logos as Logos<'a>>::Source as logos::Source>::slice_unchecked(
        cache.input,
        *range.start..*range.end,
      )
    }
  }

  #[inline(always)]
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

/// The state trait for lexers
pub trait State: core::fmt::Debug + Clone {
  /// The error type of the state.
  type Error: core::error::Error + Clone;
}

impl State for () {
  type Error = core::convert::Infallible;
}

/// Tokenizer trait
pub trait Tokenizer<'a, T: Token<'a>>:
  SliceInput<'a> + ValueInput<'a, Span = utils::Span, Token = Lexed<'a, T>>
{
}

impl<'a, T, I> Tokenizer<'a, T> for I
where
  I: SliceInput<'a> + ValueInput<'a, Span = utils::Span, Token = Lexed<'a, T>>,
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: State,
{
}
