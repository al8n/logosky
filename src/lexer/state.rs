pub use recursion_tracker::*;
pub use token_tracker::*;
pub use tracker::*;

mod recursion_tracker;
mod token_tracker;
mod tracker;

/// The state of the lexer.
pub trait State: Copy + core::fmt::Debug {
  /// The error type of the state
  type Error: core::error::Error + Clone;

  /// Increases the token count.
  fn increase_token(&mut self);

  /// Increases the recursion depth
  fn increase_recursion(&mut self);

  /// Decreases the recursion depth.
  fn decrease_recursion(&mut self);

  /// Checks the state, returning an error if the state is invalid.
  ///
  /// This function will be automatically invoked when yielding every token,
  /// if an error is returned than a state error token will be created by
  /// [`Token::from_state_error`](super::Token::from_state_error)
  fn check(&self) -> Result<(), Self::Error>;
}

impl State for () {
  type Error = core::convert::Infallible;

  #[inline(always)]
  fn increase_token(&mut self) {}

  #[inline(always)]
  fn increase_recursion(&mut self) {}

  #[inline(always)]
  fn decrease_recursion(&mut self) {}

  #[inline(always)]
  fn check(&self) -> Result<(), Self::Error> {
    Ok(())
  }
}
