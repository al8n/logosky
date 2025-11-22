pub use source::Source;
pub use token::{
  DelimiterToken, IdentifierToken, KeywordToken, Lexed, LitToken, Logos, OperatorToken,
  PunctuatorToken, Require, Token, TriviaToken,
};
pub use tokenizer::*;

use crate::utils::Span;

/// The token related structures and traits
pub mod token;

/// The source related structures and traits
pub mod source;

mod tokenizer;

/// A trait for lexers
pub trait Lexer<'source, T> {
  /// The state of the lexer.
  type State: State;

  /// Lexes the input source and returns a tokenizer.
  fn new(src: &'source T::Source) -> Self
  where
    Self::State: Default,
    T: Token<'source>;

  /// Lexes the input source with the given initial state and returns a tokenizer.
  fn with_state(src: &'source T::Source, state: Self::State) -> Self
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

  /// Consumes the lexer and returns the current state.
  fn into_state(self) -> Self::State;

  /// Returns a reference to the source being lexed.
  fn source(&self) -> &'source T::Source
  where
    T: Token<'source>;

  /// Get the range for the current token in `Source`.
  fn span(&self) -> Span;

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

impl<'source, T, L> Lexer<'source, T> for logos::Lexer<'source, L>
where
  T: From<L> + Token<'source, Source = L::Source>,
  T::Error: From<L::Error> + From<<L::Extras as State>::Error>,
  L: logos::Logos<'source>,
  L::Extras: State,
  L::Source: Source,
{
  type State = L::Extras;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn new(src: &'source T::Source) -> Self
  where
    Self::State: Default,
  {
    logos::Lexer::new(src)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn with_state(src: &'source T::Source, state: Self::State) -> Self {
    logos::Lexer::with_extras(src, state)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn state(&self) -> &Self::State {
    &self.extras
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn check(&self) -> Result<(), T::Error>
  where
    T: Token<'source>,
  {
    self.extras.check().map_err(Into::into)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_state(self) -> Self::State {
    self.extras
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn source(&self) -> &'source T::Source
  where
    T: Token<'source>,
  {
    self.source()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn span(&self) -> Span {
    self.span().into()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn lex(&mut self) -> Option<Result<T, T::Error>>
  where
    T: Token<'source>,
  {
    match self.next() {
      Some(Ok(tok)) => match <Self as Lexer<'_, T>>::check(self) {
        Ok(()) => Some(Ok(T::from(tok))),
        Err(err) => Some(Err(err)),
      },
      Some(Err(err)) => Some(Err(err.into())),
      None => None,
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn bump(&mut self, n: usize) {
    self.bump(n);
  }
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
