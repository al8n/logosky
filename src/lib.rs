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

/// A trait for types that can be parsed from a [`Tokenizer`].
pub trait Parseable<'a, I>
where
  I: Tokenizer<'a, Self::Token, Slice = <<Self::Token as Logos<'a>>::Source as Source>::Slice<'a>>,
{
  /// The token type produced by the tokenizer.
  type Token: Token<'a>;
  /// The error type for parsing.
  type Error: 'a;

  /// Returns a parser that can parse `Self` from the given tokenizer.
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E>
  where
    Self: Sized,
    E: chumsky::extra::ParserExtra<'a, I, Error = Self::Error>;
}

#[doc(hidden)]
pub mod __private {
  pub use super::lexer::{FromLexError, Require, Tokenizer, token};
  pub use chumsky;
  pub use logos;
}
