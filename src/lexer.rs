use core::ops::Range;

pub use source::Source;
pub use token::{Lexed, Logos, LosslessToken, Token, TokenExt};

use crate::utils;

/// The token related structures and traits
pub mod token;

/// The source related structures and traits
pub mod source;


#[cfg(feature = "chumsky")]
#[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
pub use tokenizer::*;

#[cfg(feature = "chumsky")]
mod tokenizer;

/// A trait for types that can be lexed from the input.
///
/// This trait provides a standardized way to lex (tokenize) an entire input
/// into a structured type. It's useful for types that represent complete
/// lexical structures that can be built from an input source.
///
/// # Type Parameters
///
/// - `I`: The input type to lex from (e.g., `&str`, `&[u8]`)
/// - `Error`: The error type returned when lexing fails
///
/// # Example
///
/// ```rust,ignore
/// use logosky::Lexable;
///
/// struct Document {
///     tokens: Vec<Token>,
/// }
///
/// impl Lexable<&str, LexError> for Document {
///     fn lex(input: &str) -> Result<Self, LexError> {
///         // Lex the entire input into a Document
///         let tokens = tokenize(input)?;
///         Ok(Document { tokens })
///     }
/// }
/// ```
pub trait Lexable<I, Error> {
  /// Lexes `Self` from the given input.
  ///
  /// This method consumes the input and attempts to construct `Self` by
  /// lexing the entire input. It returns an error if the input cannot be
  /// successfully lexed.
  ///
  /// # Errors
  ///
  /// Returns an error if the input is malformed or cannot be lexed according
  /// to the rules of the implementing type.
  fn lex(input: I) -> Result<Self, Error>
  where
    Self: Sized;
}

/// The state trait for lexers
pub trait State: core::fmt::Debug + Clone {
  /// The error type of the state.
  type Error: core::error::Error + Clone;
}

impl State for () {
  type Error = core::convert::Infallible;
}
