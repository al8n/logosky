#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

pub use chumsky;
pub use logos;

pub use lexer::*;

mod lexer;

/// Common utilities for working with tokens and lexers.
pub mod utils;

/// A trait for types that can be parsed directly from a [`I: Tokenizer<'a, T>`](Tokenizer) which yields [`T: Token<'a>`](Token) and may produce an `Error`.
pub trait Parseable<'a, I, T, Error> {
  /// Returns a parser that can parse `Self` from the given tokenizer.
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    I: Tokenizer<'a, T, Slice = <T::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a;
}

impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for utils::Spanned<D>
where
  D: Parseable<'a, I, T, Error>,
{
  #[inline(always)]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
    I: Tokenizer<'a, T, Slice = <T::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
  {
    use chumsky::Parser;

    <D as Parseable<'a, I, T, Error>>::parser()
      .map_with(|value, exa| utils::Spanned::new(exa.span(), value))
  }
}

#[doc(hidden)]
pub mod __private {
  pub use super::lexer::{FromLexError, Require, Tokenizer, token};
  pub use chumsky;
  pub use logos;
}
