#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

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

#[doc(hidden)]
pub mod __private {
  pub use super::lexer::{FromLexError, Require, Tokenizer, token};
  pub use chumsky;
  pub use logos;
}
