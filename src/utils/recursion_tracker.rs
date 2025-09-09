/// An error that occurs when the recursion limit is exceeded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, thiserror::Error)]
#[error("recursion limit exceeded: depth {}, maximum {}", .0.depth(), .0.limitation())]
pub struct RecursionLimitExceeded(RecursionLimiter);

impl RecursionLimitExceeded {
  /// Returns the recursion tracker that caused the error.
  #[inline(always)]
  pub const fn depth(&self) -> usize {
    self.0.depth()
  }

  /// Returns the maximum number of recursion limitation.
  #[inline(always)]
  pub const fn limitation(&self) -> usize {
    self.0.limitation()
  }
}

/// A recursion tracker which tracks the depth of the recursion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecursionLimiter {
  max: usize,
  current: usize,
}

impl Default for RecursionLimiter {
  #[inline(always)]
  fn default() -> Self {
    Self::new()
  }
}

impl RecursionLimiter {
  /// Creates a new recursion tracker.
  ///
  /// Defaults to a maximum depth of 500.
  #[inline(always)]
  pub const fn new() -> Self {
    Self {
      max: 500,
      current: 0,
    }
  }

  /// Creates a new recursion tracker with the given maximum depth.
  #[inline(always)]
  pub const fn with_limitation(max: usize) -> Self {
    Self { max, current: 0 }
  }

  /// Returns the current depth of the recursion.
  #[inline(always)]
  pub const fn depth(&self) -> usize {
    self.current
  }

  /// Returns the maximum depth of the recursion.
  #[inline(always)]
  pub const fn limitation(&self) -> usize {
    self.max
  }

  /// Increase the current depth of the recursion.
  #[inline(always)]
  pub const fn increase(&mut self) {
    self.current += 1;
  }

  /// Decrease the current depth of the recursion.
  #[inline(always)]
  pub const fn decrease(&mut self) {
    self.current = self.current.saturating_sub(1);
  }

  /// Increases the recursion depth.
  #[inline(always)]
  pub const fn increase_recursion(&mut self) {
    self.increase();
  }

  /// Decrease the current depth of the recursion.
  #[inline(always)]
  pub const fn decrease_recursion(&mut self) {
    self.decrease();
  }

  /// Checks if the recursion limit has been exceeded.
  #[inline(always)]
  pub const fn check(&self) -> Result<(), RecursionLimitExceeded> {
    if self.depth() > self.limitation() {
      Err(RecursionLimitExceeded(*self))
    } else {
      Ok(())
    }
  }
}
