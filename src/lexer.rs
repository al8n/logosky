pub use cache::*;
pub use checkpoint::Checkpoint;
pub use cursor::Cursor;
pub use emitter::Emitter;
pub use source::Source;
pub use token::{
  DelimiterToken, IdentifierToken, KeywordToken, Lexed, LitToken, Logos, OperatorToken,
  PunctuatorToken, Require, Token, TriviaToken,
};
pub use input::Input;
pub use input_ref::InputRef;

use crate::utils::{Span, Spanned};

/// The token related structures and traits
pub mod token;

/// The source related structures and traits
pub mod source;

mod cache;
mod checkpoint;
mod cursor;
mod emitter;
mod logos;
mod input;
mod input_ref;

/// A trait for lexers
pub trait Lexer<'source, T> {
  /// The state of the lexer.
  type State: State;
  /// The source type of the lexer.
  type Source: super::Source + ?Sized;
  /// The cursor type of the lexer.
  type Cursor;

  /// Lexes the input source and returns a tokenizer.
  fn new(src: &'source Self::Source) -> Self
  where
    Self::State: Default,
    T: Token<'source>;

  /// Lexes the input source with the given initial state and returns a tokenizer.
  fn with_state(src: &'source Self::Source, state: Self::State) -> Self
  where
    T: Token<'source>;

  /// Checks the current state of the lexer for errors.
  ///
  /// If the state is valid, returns `Ok(())`, otherwise returns an error.
  fn check(&self) -> Result<(), T::Error>
  where
    T: Token<'source>;

  /// Returns a reference to the current state of the lexer.
  fn state(&self) -> &Self::State;

  /// Returns a mutable reference to the current state of the lexer.
  fn state_mut(&mut self) -> &mut Self::State;

  /// Consumes the lexer and returns the current state.
  fn into_state(self) -> Self::State;

  /// Returns a reference to the source being lexed.
  fn source(&self) -> &'source Self::Source
  where
    T: Token<'source>;

  /// Get the range for the current token in `Source`.
  fn span(&self) -> Span;

  /// Returns the slice of the current token in the source.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self) -> Option<<Self::Source as Source>::Slice<'source>> where T: Token<'source> {
    self.source().slice(self.span().into())
  }

  /// Lexes the next token from the input source.
  fn lex(&mut self) -> Option<Result<T, T::Error>>
  where
    T: Token<'source>;

  /// Bumps the end of currently lexed token by `n` offsets.
  ///
  /// # Panics
  ///
  /// Panics if adding `n` to current offset would place the `Lexer` beyond the last byte,
  /// or in the middle of an UTF-8 code point (does not apply when lexing raw `&[u8]`).
  fn bump(&mut self, n: usize);
}

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

  /// Checks the state for errors.
  fn check(&self) -> Result<(), Self::Error>;
}

impl State for () {
  type Error = core::convert::Infallible;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn check(&self) -> Result<(), Self::Error> {
    Ok(())
  }
}

/// A cached token with its associated extras.
pub struct CachedToken<'a, T: Token<'a>, L: Lexer<'a, T>> {
  token: Spanned<Lexed<'a, T>>,
  state: L::State,
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>> Clone for CachedToken<'a, T, L>
where
  L::State: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      token: self.token.clone(),
      state: self.state.clone(),
    }
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>> CachedToken<'a, T, L> {
  /// Creates a new cached token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new(token: Spanned<Lexed<'a, T>>, state: L::State) -> Self {
    Self { token, state }
  }

  /// Returns a reference to the token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn token(&self) -> &Spanned<Lexed<'a, T>> {
    &self.token
  }

  /// Consumes the cached token and returns the lexed token.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_token(self) -> Spanned<Lexed<'a, T>> {
    self.token
  }

  /// Returns a reference to the state.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn state(&self) -> &L::State {
    &self.state
  }

  /// Consumes the cached token and returns the extras.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Spanned<Lexed<'a, T>>, L::State) {
    (self.token, self.state)
  }
}

/// A black hole cache that discards all tokens.
///
/// `BlackHole` implements the [`Cache`] trait but doesn't actually store any tokens.
/// All tokens pushed to it are immediately discarded. This is useful when you want to
/// process tokens in a streaming fashion without maintaining a lookahead buffer.
#[derive(Debug, Clone, Copy, Default)]
pub struct BlackHole;
