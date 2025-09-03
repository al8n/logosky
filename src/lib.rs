#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

pub use lexer::*;

mod lexer;

#[doc(hidden)]
mod __private {
  pub use super::lexer::{Tokenizer, FromLexError, Require, token};
  pub use chumsky;
}
