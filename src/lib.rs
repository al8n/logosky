#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![allow(clippy::double_parens)]
#![deny(missing_docs, warnings)]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

pub use logos;

pub use lexer::*;
mod lexer;

/// Concrete Syntax Tree (CST) representations and utilities.
#[cfg(feature = "rowan")]
#[cfg_attr(docsrs, doc(cfg(feature = "rowan")))]
pub mod cst;

/// Common utilities for working with tokens and lexers.
pub mod utils;

/// Re-exports for chumsky integration.
#[cfg(feature = "chumsky")]
#[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
pub mod chumsky;

#[cfg(feature = "chumsky")]
#[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
pub use chumsky::LogoStream;

mod keyword;
mod punct;

#[doc(hidden)]
pub mod __private {
  pub use super::{lexer::token, utils};

  #[cfg(feature = "chumsky")]
  #[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
  pub use chumsky;
  pub use logos;

  #[cfg(any(feature = "std", feature = "alloc"))]
  pub use std::{boxed::Box, string::String, vec::Vec};
}
