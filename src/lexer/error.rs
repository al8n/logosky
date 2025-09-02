use std::{borrow::Cow, string::String};

use chumsky::{
  error::{EmptyErr, Rich, RichPattern, Simple},
  label::LabelError,
  span::SimpleSpan,
  util::{Maybe, MaybeRef},
};

use super::*;

/// The lexer error
#[derive(Debug, Clone, derive_more::IsVariant)]
pub enum LexerError<'a, T>
where
  T: Token<'a>,
{
  /// The token error happens when trying to pull the next token.
  Token(T::Error),
  /// The unexpected token error
  UnexpectedToken {
    /// The expected token name
    expected: Cow<'static, str>,
    /// The actual token found.
    found: T,
  },
  /// End of input
  EndOfInput,
  /// The other error message
  Other(Cow<'static, str>),
}

impl<'a, T> core::fmt::Display for LexerError<'a, T>
where
  T: Token<'a>,
  T::Error: core::fmt::Display,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Token(tok) => tok.fmt(f),
      Self::UnexpectedToken { expected, found } => {
        write!(f, "unexpected token: expected {expected}, found {found}")
      }
      Self::EndOfInput => write!(f, "unexpected end of input"),
      Self::Other(cow) => write!(f, "{cow}"),
    }
  }
}

impl<'a, T> core::error::Error for LexerError<'a, T>
where
  T: Token<'a>,
  T::Error: core::fmt::Display,
{}

impl<'a, T> LexerError<'a, T>
where
  T: Token<'a>,
{
  /// Creates a token error data
  #[inline]
  pub const fn token(data: T::Error) -> Self {
    Self::Token(data)
  }

  /// Creates a unexpected token error
  #[inline]
  pub fn unexpected_token(expected: impl Into<Cow<'static, str>>, found: T) -> Self {
    Self::UnexpectedToken { expected: expected.into(), found }
  }

  /// Creates a new end of input error
  #[inline]
  pub fn end_of_input() -> Self {
    Self::EndOfInput
  }

  /// Creates a new other error
  #[inline]
  pub fn other(msg: impl Into<Cow<'static, str>>) -> Self {
    Self::Other(msg.into())
  }
}

impl<'a, T> From<&'static str> for LexerError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: &'static str) -> Self {
    Self::Other(Cow::Borrowed(e))
  }
}

impl<'a, T> From<String> for LexerError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: String) -> Self {
    Self::Other(Cow::Owned(e))
  }
}

impl<'a, T> From<Cow<'static, str>> for LexerError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: Cow<'static, str>) -> Self {
    Self::Other(e)
  }
}

impl<'a, T, L> LabelError<'a, TokenStream<'a, T>, L> for Simple<'a, T, Span<T::Extras>> 
where
  T: Token<'a>,
  T::Extras: Copy,
{
  fn expected_found<E: IntoIterator<Item = L>>(
    _expected: E,
    found: Option<MaybeRef<'a, TokenResult<'a, T>>>,
    span: Span<T::Extras>,
  ) -> Self {
    match found {
      Some(Maybe::Ref(Ok(tok))) => Simple::new(Some(Maybe::Ref(tok)), span),
      Some(Maybe::Val(Ok(tok))) => Simple::new(Some(Maybe::Val(tok)), span),
      _ => Simple::new(None, span),
    }
  }
}

impl<'a, T> From<LexerError<'a, T>> for RichPattern<'a, T>
where
  T: Token<'a>,
  T::Error: core::fmt::Display,
{
  #[inline(always)]
  fn from(value: LexerError<'a, T>) -> Self {
    match value {
      LexerError::UnexpectedToken { expected, found } => {
        Self::Label(format!("unexpected token: expected {expected}, found {found}").into())
      }
      LexerError::Token(err) => Self::Label(err.to_string().into()),
      LexerError::EndOfInput => Self::EndOfInput,
      LexerError::Other(cow) => Self::Label(cow),
    }
  }
}


impl<'a, T> LabelError<'a, TokenStream<'a, T>, LexerError<'a, T>> for Rich<'a, T, Span<T::Extras>> 
where
  T: Token<'a>,
  T::Error: core::fmt::Display,
  T::Extras: Copy,
{
  fn expected_found<E: IntoIterator<Item = LexerError<'a, T>>>(
    expected: E,
    found: Option<MaybeRef<'a, TokenResult<'a, T>>>,
    span: Span<T::Extras>,
  ) -> Self {
    match found {
      Some(Maybe::Ref(Ok(tok))) => Self::custom(span, tok),
      Some(Maybe::Val(Ok(tok))) => Self::new(Some(Maybe::Val(tok)), span),
      _ => Self::new(None, span),
    }
  }
}
