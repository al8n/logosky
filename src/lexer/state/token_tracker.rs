/// An error that occurs when the token limit is exceeded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, thiserror::Error)]
#[error("token limit exceeded: tokens {}, maximum {}", .0.tokens(), .0.limitation())]
pub struct TokenLimitExceeded(TokenLimiter);

impl TokenLimitExceeded {
  /// Returns the token tracker that caused the error.
  #[inline(always)]
  pub const fn tokens(&self) -> usize {
    self.0.tokens()
  }

  /// Returns the maximum number of tokens limitation.
  #[inline(always)]
  pub const fn limitation(&self) -> usize {
    self.0.limitation()
  }
}

/// A token tracker which tracks the number of tokens.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TokenLimiter {
  max: usize,
  current: usize,
}

impl TokenLimiter {
  /// Creates a new token tracker without limitation.
  #[inline(always)]
  pub const fn new() -> Self {
    Self {
      max: usize::MAX,
      current: 0,
    }
  }

  /// Creates a new token tracker with the given maximum number of tokens
  #[inline(always)]
  pub const fn with_limitation(max: usize) -> Self {
    Self { max, current: 0 }
  }

  /// Returns the current number of tokens tracked.
  #[inline(always)]
  pub const fn tokens(&self) -> usize {
    self.current
  }

  /// Increase the number of tokens by one.
  #[inline(always)]
  pub const fn increase(&mut self) {
    self.current += 1;
  }

  /// Returns the maximum number of tokens.
  #[inline(always)]
  pub const fn limitation(&self) -> usize {
    self.max
  }
}

impl super::State for TokenLimiter {
  type Error = TokenLimitExceeded;

  #[inline(always)]
  fn increase_token(&mut self) {
    self.increase();
  }

  #[inline(always)]
  fn increase_recursion(&mut self) {}

  #[inline(always)]
  fn decrease_recursion(&mut self) {}

  #[inline]
  fn check(&self) -> Result<(), Self::Error> {
    if self.tokens() > self.limitation() {
      Err(TokenLimitExceeded(*self))
    } else {
      Ok(())
    }
  }
}
