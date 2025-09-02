use core::{
  marker::PhantomData,
  ops::Range,
};

use chumsky::input::{ExactSizeInput, Input, ValueInput};

pub use error::*;
use logos::Logos;
pub use require::Require;
pub use source::{DisplaySource, SourceDisplay, Source, SourceExt};
pub use span::*;
pub use token::{TokenResult, Token};

mod error;
mod require;

mod span;


/// The token related structures and traits
pub mod token;

/// The source related structures and traits
pub mod source;

/// The logos token stream adapter for chumsky's parsers
#[derive(Debug, Clone, Copy)]
pub struct TokenStream<'a, T: Token<'a>> {
  input: &'a T::Source,
  state: T::Extras,
}

impl<'a, T> TokenStream<'a, T>
where
  T: Token<'a>,
  T::Extras: Default,
{
  /// Creates a new lexer from the given input.
  #[inline(always)]
  pub fn new(input: &'a T::Source) -> Self {
    Self::with_state(input, T::Extras::default())
  }
}

impl<'a, T: Token<'a>> TokenStream<'a, T> {
  /// Creates a new lexer from the given input and state.
  #[inline(always)]
  pub const fn with_state(input: &'a T::Source, state: T::Extras) -> Self {
    Self {
      input,
      state,
    }
  }
}

impl<'a, T: Token<'a>> TokenStream<'a, T> {
  /// Returns a reference to the input.
  #[inline(always)]
  pub const fn input(&self) -> &T::Source {
    self.input
  }
}

impl<'a, T> Input<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T as Logos<'a>>::Extras: Copy,
{
  type Span = span::Span<<T as Logos<'a>>::Extras>;

  type Token = TokenResult<'a, T>;

  type MaybeToken = TokenResult<'a, T>;

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
    let mut lexer = logos::Lexer::<T>::with_extras(this.input, this.state);
    lexer.bump(*cursor);
    lexer.next().inspect(|_| {
      *cursor += lexer.span().len();
      this.state = lexer.extras;
    })
  }

  #[inline(always)]
  unsafe fn span(this: &mut Self::Cache, range: Range<&Self::Cursor>) -> Self::Span {
    Span::new(*range.start, *range.end, this.state)
  }
}

impl<'a, T> ValueInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T as Logos<'a>>::Extras: Copy,
{
  #[inline(always)]
  unsafe fn next(cache: &mut Self::Cache, cursor: &mut Self::Cursor) -> Option<Self::Token> {
    unsafe { <Self as Input<'a>>::next_maybe(cache, cursor) }
  }
}

impl<'a, T> ExactSizeInput<'a> for TokenStream<'a, T>
where
  T: Token<'a>,
  <T as Logos<'a>>::Extras: Copy,
{
  #[inline(always)]
  unsafe fn span_from(
    cache: &mut Self::Cache,
    range: core::ops::RangeFrom<&Self::Cursor>,
  ) -> Self::Span {
    Span::new(*range.start, cache.input.len(), cache.state)
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  #[derive(logos::Logos, Debug, Clone, Copy, PartialEq, Eq)]
  #[logos(skip r"[ \t\n\f]+")]
  enum Tok<'a> {
    #[token("let")]
    Let,
    #[token("=")]
    Eq,
    #[token(";")]
    Semicolon,
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice())]
    Ident(&'a str),
    #[regex(r"[0-9]+")]
    Number,
    Error(()),
  }

  impl core::fmt::Display for Tok<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
      match self {
        Tok::Let => write!(f, "let"),
        Tok::Eq => write!(f, "="),
        Tok::Semicolon => write!(f, ";"),
        Tok::Ident(_) => write!(f, "identifier"),
        Tok::Number => write!(f, "number"),
        Tok::Error(_) => write!(f, "error"),
      }
    }
  }

  impl From<()> for Tok<'_> {
    fn from(value: ()) -> Self {
      Tok::Error(value)
    }
  }

  // impl<'a> super::Token<'a> for Tok {
  //   fn with_state_error(self, _err: <Self::Extras as State>::Error) -> Self
  //   where
  //     Self::Extras: State,
  //   {
  //     self
  //   }

  //   fn check(self) -> Result<Self, <Self as logos::Logos<'a>>::Error> {
  //     Ok(self)
  //   }
  // }

  #[test]
  fn test_lexer() {
    let input = "let x = 5;";
    let mut lexer = TokenStream::<Tok<'_>>::new(input);

    let mut cursor = 0;
    let tok = unsafe { <TokenStream<'_, Tok<'_>> as ValueInput>::next(&mut lexer, &mut cursor) };
    assert_eq!(tok, Some(Ok(Tok::Let)));

    let tok = unsafe { <TokenStream<'_, Tok<'_>> as ValueInput>::next(&mut lexer, &mut cursor) };
    assert_eq!(tok, Some(Ok(Tok::Ident("x"))));
  }

  // #[derive(logos::Logos, Debug, Clone, Copy, PartialEq, Eq)]
  // #[logos(skip r"[ \t\n\f]+")]
  // #[logos(source = bytes::Bytes)]
  // enum TokBytes {
  //   #[token("let")]
  //   Let,
  //   #[token("=")]
  //   Eq,
  //   #[token(";")]
  //   Semicolon,
  //   #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
  //   Ident,
  //   #[regex(r"[0-9]+")]
  //   Number,
  //   Error(()),
  // }

  // impl core::fmt::Display for TokBytes {
  //   fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
  //     match self {
  //       Self::Let => write!(f, "let"),
  //       Self::Eq => write!(f, "="),
  //       Self::Semicolon => write!(f, ";"),
  //       Self::Ident => write!(f, "identifier"),
  //       Self::Number => write!(f, "number"),
  //       Self::Error(_) => write!(f, "error"),
  //     }
  //   }
  // }

  // impl From<()> for TokBytes {
  //   fn from(value: ()) -> Self {
  //     Self::Error(value)
  //   }
  // }

  // // impl<'a> super::Token<'a> for TokBytes {
  // //   fn with_state_error(self, _err: <Self::Extras as State>::Error) -> Self
  // //   where
  // //     Self::Extras: State,
  // //   {
  // //     self
  // //   }

  // //   fn check(self) -> Result<Self, <Self as logos::Logos<'a>>::Error> {
  // //     Ok(self)
  // //   }
  // // }

  // #[test]
  // fn test_lexer_bytes() {
  //   let input = bytes::Bytes::from_static(b"let x = 5;");
  //   let mut lexer = TokenStream::<_, TokBytes>::new(&input);

  //   let mut cursor = 0;
  //   let tok = unsafe { <TokenStream<'_, _, TokBytes> as ValueInput>::next(&mut lexer, &mut cursor) };
  //   assert_eq!(tok, Some(Ok(TokBytes::Let)));

  //   let tok = unsafe { <TokenStream<'_, _, TokBytes> as ValueInput>::next(&mut lexer, &mut cursor) };
  //   assert_eq!(tok, Some(Ok(TokBytes::Ident)));
  // }
}
