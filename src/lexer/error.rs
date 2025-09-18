use std::{borrow::Cow, string::String};

use chumsky::{
  error::{Cheap, EmptyErr, RichPattern, Simple},
  label::LabelError,
  util::{Maybe, MaybeRef},
};

use super::*;

use crate::utils::Span;

/// The lexer error
#[derive(Debug, Clone, derive_more::IsVariant)]
pub enum LexError<'a, T>
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

impl<'a, T> core::fmt::Display for LexError<'a, T>
where
  T: Token<'a> + core::fmt::Display,
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

impl<'a, T> core::error::Error for LexError<'a, T>
where
  T: Token<'a> + core::fmt::Display,
  T::Error: core::fmt::Display,
{
}

impl<'a, T> LexError<'a, T>
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
    Self::UnexpectedToken {
      expected: expected.into(),
      found,
    }
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

impl<'a, T> From<&'static str> for LexError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: &'static str) -> Self {
    Self::Other(Cow::Borrowed(e))
  }
}

impl<'a, T> From<String> for LexError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: String) -> Self {
    Self::Other(Cow::Owned(e))
  }
}

impl<'a, T> From<Cow<'static, str>> for LexError<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn from(e: Cow<'static, str>) -> Self {
    Self::Other(e)
  }
}

impl<'a, T, S> FromLexError<'a, T, S> for EmptyErr
where
  T: Token<'a>,
  T::Extras: Copy,
{
  #[inline]
  fn from_lex_error(_: T::Error, _: S) -> Self
  where
    T: Token<'a>,
  {
    EmptyErr::default()
  }
}

impl<'a, T, S> FromLexError<'a, T, S> for Cheap<S>
where
  T: Token<'a>,
  T::Extras: Copy,
{
  #[inline]
  fn from_lex_error(_: T::Error, span: S) -> Self
  where
    T: Token<'a>,
  {
    Cheap::new(span)
  }
}

impl<'a, T, L> LabelError<'a, TokenStream<'a, T>, L> for Simple<'a, T, Span>
where
  T: Token<'a>,
  T::Extras: Copy,
{
  fn expected_found<E: IntoIterator<Item = L>>(
    _expected: E,
    found: Option<MaybeRef<'a, Lexed<'a, T>>>,
    span: Span,
  ) -> Self {
    match found {
      Some(Maybe::Ref(Lexed::Token(tok))) => Simple::new(Some(Maybe::Ref(tok.data())), span),
      Some(Maybe::Val(Lexed::Token(tok))) => Simple::new(Some(Maybe::Val(tok.into_data())), span),
      _ => Simple::new(None, span),
    }
  }
}

impl<'a, T, S> FromLexError<'a, T, S> for Simple<'a, T::Error, S>
where
  T: Token<'a>,
  T::Extras: Copy,
{
  #[inline]
  fn from_lex_error(value: T::Error, span: S) -> Self
  where
    T: Token<'a>,
  {
    Self::new(Some(Maybe::Val(value)), span)
  }
}

impl<'a, T> From<LexError<'a, T>> for RichPattern<'a, T>
where
  T: Token<'a> + core::fmt::Display,
  T::Error: core::fmt::Display,
{
  #[inline(always)]
  fn from(value: LexError<'a, T>) -> Self {
    match value {
      LexError::UnexpectedToken { expected, found } => {
        Self::Label(std::format!("unexpected token: expected {expected}, found {found}").into())
      }
      LexError::Token(err) => Self::Label(err.to_string().into()),
      LexError::EndOfInput => Self::EndOfInput,
      LexError::Other(cow) => Self::Label(cow),
    }
  }
}

/// A trait for converting a lexer error into the target error.
pub trait FromLexError<'a, T, S> {
  /// Converts a lexer error into the target error with the span
  fn from_lex_error(err: T::Error, span: S) -> Self
  where
    T: Token<'a>;
}
