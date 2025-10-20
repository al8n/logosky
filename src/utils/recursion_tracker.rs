use crate::State;

/// Error returned when recursion depth exceeds the configured limit.
///
/// This error provides context about both the actual recursion depth reached
/// and the maximum depth allowed, making it easy to diagnose whether the limit
/// needs adjustment or if there's a genuine infinite recursion bug.
///
/// # Example
///
/// ```rust
/// use logosky::utils::recursion_tracker::{RecursionLimiter, RecursionLimitExceeded};
///
/// let mut limiter = RecursionLimiter::with_limitation(10);
///
/// // Simulate deep recursion
/// for _ in 0..15 {
///     limiter.increase();
/// }
///
/// match limiter.check() {
///     Err(error) => {
///         eprintln!("Recursion limit exceeded!");
///         eprintln!("Current depth: {}", error.depth());
///         eprintln!("Maximum allowed: {}", error.limitation());
///     }
///     Ok(_) => unreachable!(),
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, thiserror::Error)]
#[error("recursion limit exceeded: depth {}, maximum {}", .0.depth(), .0.limitation())]
pub struct RecursionLimitExceeded(RecursionLimiter);

impl RecursionLimitExceeded {
  /// Returns the actual recursion depth that triggered the error.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::recursion_tracker::{RecursionLimiter, RecursionLimitExceeded};
  ///
  /// let mut limiter = RecursionLimiter::with_limitation(3);
  /// limiter.increase();
  /// assert_eq!(limiter.depth(), 1);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn depth(&self) -> usize {
    self.0.depth()
  }

  /// Returns the maximum recursion depth that was configured.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::recursion_tracker::{RecursionLimiter, RecursionLimitExceeded};
  ///
  /// let mut limiter = RecursionLimiter::with_limitation(3);
  /// assert_eq!(limiter.limitation(), 3);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn limitation(&self) -> usize {
    self.0.limitation()
  }
}

/// A recursion depth tracker that prevents stack overflow in recursive parsers.
///
/// `RecursionLimiter` helps protect against infinite recursion by tracking the current
/// recursion depth and enforcing a maximum depth limit. This is essential for parsers
/// that use recursive descent, as deeply nested or circular grammar rules can easily
/// cause stack overflow.
///
/// # Default Limit
///
/// The default maximum depth is **500**, which is conservative enough to prevent stack
/// overflow on most platforms while allowing reasonably deep nesting.
///
/// # Use Cases
///
/// - **Recursive descent parsers**: Track depth through grammar rules
/// - **AST traversal**: Prevent stack overflow on deeply nested trees
/// - **Expression evaluation**: Limit nesting in arithmetic/boolean expressions
/// - **Stateful lexers**: Track depth in the lexer's `Extras` state
///
/// # Integration with LogoSky
///
/// `RecursionLimiter` can be used as part of a Logos lexer's `Extras` state by
/// implementing the [`State`] trait, allowing you to track recursion
/// during lexing.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// let mut limiter = RecursionLimiter::new();
///
/// limiter.increase(); // Enter recursion
/// assert_eq!(limiter.depth(), 1);
///
/// limiter.increase(); // Go deeper
/// assert_eq!(limiter.depth(), 2);
///
/// limiter.decrease(); // Return from recursion
/// assert_eq!(limiter.depth(), 1);
///
/// limiter.decrease();
/// assert_eq!(limiter.depth(), 0);
/// ```
///
/// ## Custom Limit
///
/// ```rust
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// // Allow deeper nesting for complex grammars
/// let mut limiter = RecursionLimiter::with_limitation(1000);
///
/// assert_eq!(limiter.limitation(), 1000);
/// ```
///
/// ## Checking Limits
///
/// ```rust
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// let mut limiter = RecursionLimiter::with_limitation(5);
///
/// for _ in 0..5 {
///     limiter.increase();
///     assert!(limiter.check().is_ok()); // Still within limit
/// }
///
/// limiter.increase(); // One too many
/// assert!(limiter.check().is_err()); // Limit exceeded!
/// ```
///
/// ## Recursive Parser Example
///
/// ```rust,ignore
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// fn parse_expr(input: &str, limiter: &mut RecursionLimiter) -> Result<Expr, Error> {
///     limiter.increase();
///     limiter.check()?; // Fail fast if too deep
///
///     let result = match input.chars().next() {
///         Some('(') => {
///             // Recursively parse nested expression
///             let nested = parse_expr(&input[1..], limiter)?;
///             Expr::Paren(Box::new(nested))
///         }
///         Some(c) if c.is_numeric() => Expr::Number(c.to_digit(10).unwrap()),
///         _ => return Err(Error::Unexpected),
///     };
///
///     limiter.decrease(); // Return from recursion
///     Ok(result)
/// }
/// ```
///
/// ## With Logos Lexer State
///
/// ```rust,ignore
/// use logos::Logos;
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// #[derive(Default)]
/// struct LexerState {
///     recursion: RecursionLimiter,
/// }
///
/// #[derive(Logos, Debug)]
/// #[logos(extras = LexerState)]
/// enum Token {
///     #[regex(r"\(", |lex| {
///         lex.extras.recursion.increase();
///         lex.extras.recursion.check().ok()
///     })]
///     LParen(()),
///
///     #[regex(r"\)", |lex| {
///         lex.extras.recursion.decrease();
///         Some(())
///     })]
///     RParen,
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RecursionLimiter {
  max: usize,
  current: usize,
}

impl Default for RecursionLimiter {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self::new()
  }
}

impl RecursionLimiter {
  /// Creates a new recursion tracker.
  ///
  /// Defaults to a maximum depth of 500.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new() -> Self {
    Self {
      max: 500,
      current: 0,
    }
  }

  /// Creates a new recursion tracker with the given maximum depth.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_limitation(max: usize) -> Self {
    Self { max, current: 0 }
  }

  /// Returns the current depth of the recursion.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn depth(&self) -> usize {
    self.current
  }

  /// Returns the maximum depth of the recursion.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn limitation(&self) -> usize {
    self.max
  }

  /// Increase the current depth of the recursion.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn increase(&mut self) {
    self.current += 1;
  }

  /// Decrease the current depth of the recursion.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn decrease(&mut self) {
    self.current = self.current.saturating_sub(1);
  }

  /// Increases the recursion depth.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn increase_recursion(&mut self) {
    self.increase();
  }

  /// Decrease the current depth of the recursion.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn decrease_recursion(&mut self) {
    self.decrease();
  }

  /// Checks if the recursion limit has been exceeded.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn check(&self) -> Result<(), RecursionLimitExceeded> {
    if self.depth() > self.limitation() {
      Err(RecursionLimitExceeded(*self))
    } else {
      Ok(())
    }
  }
}

impl State for RecursionLimiter {
  type Error = RecursionLimitExceeded;
}
