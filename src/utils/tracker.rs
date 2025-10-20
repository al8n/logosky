use crate::State;

use super::{
  recursion_tracker::{RecursionLimitExceeded, RecursionLimiter},
  token_tracker::{TokenLimitExceeded, TokenLimiter},
};

/// Error returned when either token or recursion limits are exceeded.
///
/// This enum combines both [`TokenLimitExceeded`] and [`RecursionLimitExceeded`]
/// errors, making it easy to handle both limit types uniformly when using
/// the [`Tracker`] type.
///
/// # Variants
///
/// - **Token**: The token count limit was exceeded
/// - **Recursion**: The recursion depth limit was exceeded
///
/// # Derived Helpers
///
/// This type provides several helper methods via derive macros:
/// - `is_token()` / `is_recursion()`: Check which variant it is
/// - `unwrap_token()` / `unwrap_recursion()`: Extract the inner error (panics if wrong variant)
/// - `try_unwrap_token()` / `try_unwrap_recursion()`: Try to extract the inner error
///
/// # Examples
///
/// ## Pattern Matching
///
/// ```rust
/// use logosky::utils::tracker::{Tracker, LimitExceeded};
///
/// let mut tracker = Tracker::new();
/// // ... use tracker ...
///
/// match tracker.check() {
///     Ok(_) => println!("All limits OK"),
///     Err(LimitExceeded::Token(e)) => {
///         eprintln!("Token limit exceeded: {}", e);
///     }
///     Err(LimitExceeded::Recursion(e)) => {
///         eprintln!("Recursion limit exceeded: {}", e);
///     }
/// }
/// ```
///
/// ## Using Derived Methods
///
/// ```rust
/// use logosky::utils::tracker::{Tracker, LimitExceeded};
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// let mut tracker = Tracker::with_recursion_tracker(
///     RecursionLimiter::with_limitation(2)
/// );
///
/// tracker.increase_recursion();
/// tracker.increase_recursion();
/// tracker.increase_recursion(); // Exceeds limit
///
/// if let Err(error) = tracker.check() {
///     assert!(error.is_recursion());
///     let recursion_error = error.unwrap_recursion();
///     assert_eq!(recursion_error.depth(), 3);
/// }
/// ```
#[derive(
  Debug,
  Clone,
  Copy,
  PartialEq,
  Eq,
  thiserror::Error,
  derive_more::IsVariant,
  derive_more::Unwrap,
  derive_more::TryUnwrap,
)]
#[unwrap(ref)]
#[try_unwrap(ref)]
pub enum LimitExceeded {
  /// The token limit has been exceeded.
  #[error(transparent)]
  Token(#[from] TokenLimitExceeded),
  /// The recursion limit has been exceeded.
  #[error(transparent)]
  Recursion(#[from] RecursionLimitExceeded),
}

/// A combined limiter that tracks both token count and recursion depth.
///
/// `Tracker` brings together [`TokenLimiter`] and [`RecursionLimiter`] into a single
/// type, providing comprehensive protection against both DoS attacks (via token limiting)
/// and stack overflow (via recursion limiting). This is the recommended choice for
/// production parsers that need robust safety guarantees.
///
/// # Components
///
/// 1. **Token Limiter**: Tracks total number of tokens processed
/// 2. **Recursion Limiter**: Tracks current recursion depth
///
/// Both limits are checked simultaneously by the [`check`](Self::check) method, which
/// returns an error if either limit is exceeded.
///
/// # Default Configuration
///
/// - **Token limit**: Unlimited (`usize::MAX`)
/// - **Recursion limit**: 500
///
/// You typically want to configure at least the token limit using
/// [`with_token_tracker`](Self::with_token_tracker) or set both limits explicitly.
///
/// # Integration with LogoSky
///
/// `Tracker` implements the [`State`](crate::State) trait and can be used directly
/// as a Logos lexer's `Extras` state, providing automatic limit checking during lexing.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use logosky::utils::tracker::Tracker;
///
/// let mut tracker = Tracker::new();
///
/// // Track token processing
/// tracker.increase_token();
/// assert_eq!(tracker.token().tokens(), 1);
///
/// // Track recursion depth
/// tracker.increase_recursion();
/// assert_eq!(tracker.recursion().depth(), 1);
///
/// tracker.decrease_recursion();
/// assert_eq!(tracker.recursion().depth(), 0);
/// ```
///
/// ## Configuring Limits
///
/// ```rust
/// use logosky::utils::tracker::Tracker;
/// use logosky::utils::token_tracker::TokenLimiter;
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// let tracker = Tracker::with_trackers(
///     TokenLimiter::with_limitation(10000),
///     RecursionLimiter::with_limitation(100)
/// );
///
/// assert_eq!(tracker.token().limitation(), 10000);
/// assert_eq!(tracker.recursion().limitation(), 100);
/// ```
///
/// ## Checking Limits
///
/// ```rust
/// use logosky::utils::tracker::Tracker;
/// use logosky::utils::token_tracker::TokenLimiter;
///
/// let mut tracker = Tracker::with_token_tracker(
///     TokenLimiter::with_limitation(5)
/// );
///
/// for _ in 0..5 {
///     tracker.increase_token();
///     assert!(tracker.check().is_ok());
/// }
///
/// tracker.increase_token(); // Exceeds limit
/// assert!(tracker.check().is_err());
/// ```
///
/// ## Lexer Integration
///
/// ```rust,ignore
/// use logos::Logos;
/// use logosky::utils::tracker::Tracker;
/// use logosky::utils::token_tracker::TokenLimiter;
/// use logosky::utils::recursion_tracker::RecursionLimiter;
///
/// #[derive(Default)]
/// struct LexerState {
///     tracker: Tracker,
/// }
///
/// impl LexerState {
///     fn new() -> Self {
///         Self {
///             tracker: Tracker::with_trackers(
///                 TokenLimiter::with_limitation(10000),
///                 RecursionLimiter::with_limitation(500),
///             ),
///         }
///     }
/// }
///
/// #[derive(Logos)]
/// #[logos(extras = LexerState)]
/// enum Token {
///     #[regex(r"[a-zA-Z]+", |lex| {
///         lex.extras.tracker.increase_token();
///         lex.extras.tracker.check().ok()
///     })]
///     Word(()),
///
///     #[regex(r"\(", |lex| {
///         lex.extras.tracker.increase_token();
///         lex.extras.tracker.increase_recursion();
///         lex.extras.tracker.check().ok()
///     })]
///     LParen(()),
///
///     #[regex(r"\)", |lex| {
///         lex.extras.tracker.increase_token();
///         lex.extras.tracker.decrease_recursion();
///         Some(())
///     })]
///     RParen,
/// }
/// ```
///
/// ## Parser Integration
///
/// ```rust,ignore
/// use logosky::utils::tracker::Tracker;
///
/// struct Parser {
///     tracker: Tracker,
/// }
///
/// impl Parser {
///     fn parse_expr(&mut self, input: &str) -> Result<Expr, Error> {
///         self.tracker.increase_recursion();
///         self.tracker.increase_token();
///         self.tracker.check()?; // Check both limits
///
///         let result = match input.chars().next() {
///             Some('(') => {
///                 let nested = self.parse_expr(&input[1..])?;
///                 Expr::Paren(Box::new(nested))
///             }
///             Some(c) if c.is_numeric() => {
///                 Expr::Number(c.to_digit(10).unwrap())
///             }
///             _ => return Err(Error::Unexpected),
///         };
///
///         self.tracker.decrease_recursion();
///         Ok(result)
///     }
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Tracker {
  token_tracker: TokenLimiter,
  recursion_tracker: RecursionLimiter,
}

impl Default for Tracker {
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  fn default() -> Self {
    Self::new()
  }
}

impl Tracker {
  /// Creates a new tracker with default limits.
  ///
  /// - Token limit: Unlimited (`usize::MAX`)
  /// - Recursion limit: 500
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let tracker = Tracker::new();
  /// assert_eq!(tracker.recursion().limitation(), 500);
  /// assert_eq!(tracker.token().limitation(), usize::MAX);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn new() -> Self {
    Self::with_trackers(TokenLimiter::new(), RecursionLimiter::new())
  }

  /// Creates a new tracker with the given token limiter and default recursion limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  /// use logosky::utils::token_tracker::TokenLimiter;
  ///
  /// let tracker = Tracker::with_token_tracker(
  ///     TokenLimiter::with_limitation(10000)
  /// );
  ///
  /// assert_eq!(tracker.token().limitation(), 10000);
  /// assert_eq!(tracker.recursion().limitation(), 500);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn with_token_tracker(token_tracker: TokenLimiter) -> Self {
    Self::with_trackers(token_tracker, RecursionLimiter::new())
  }

  /// Creates a new tracker with the given recursion limiter and default token limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  /// use logosky::utils::recursion_tracker::RecursionLimiter;
  ///
  /// let tracker = Tracker::with_recursion_tracker(
  ///     RecursionLimiter::with_limitation(100)
  /// );
  ///
  /// assert_eq!(tracker.recursion().limitation(), 100);
  /// assert_eq!(tracker.token().limitation(), usize::MAX);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn with_recursion_tracker(recursion_tracker: RecursionLimiter) -> Self {
    Self::with_trackers(TokenLimiter::new(), recursion_tracker)
  }

  /// Creates a new tracker with the given token and recursion limiters.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  /// use logosky::utils::token_tracker::TokenLimiter;
  /// use logosky::utils::recursion_tracker::RecursionLimiter;
  ///
  /// let tracker = Tracker::with_trackers(
  ///     TokenLimiter::with_limitation(5000),
  ///     RecursionLimiter::with_limitation(200)
  /// );
  ///
  /// assert_eq!(tracker.token().limitation(), 5000);
  /// assert_eq!(tracker.recursion().limitation(), 200);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn with_trackers(
    token_tracker: TokenLimiter,
    recursion_tracker: RecursionLimiter,
  ) -> Self {
    Self {
      token_tracker,
      recursion_tracker,
    }
  }

  /// Returns a reference to the token limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let tracker = Tracker::new();
  /// assert_eq!(tracker.token().tokens(), 0);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn token(&self) -> &TokenLimiter {
    &self.token_tracker
  }

  /// Returns a mutable reference to the token limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let mut tracker = Tracker::new();
  /// tracker.token_mut().increase();
  /// assert_eq!(tracker.token().tokens(), 1);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn token_mut(&mut self) -> &mut TokenLimiter {
    &mut self.token_tracker
  }

  /// Returns a reference to the recursion limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let tracker = Tracker::new();
  /// assert_eq!(tracker.recursion().depth(), 0);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn recursion(&self) -> &RecursionLimiter {
    &self.recursion_tracker
  }

  /// Returns a mutable reference to the recursion limiter.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let mut tracker = Tracker::new();
  /// tracker.recursion_mut().increase();
  /// assert_eq!(tracker.recursion().depth(), 1);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn recursion_mut(&mut self) -> &mut RecursionLimiter {
    &mut self.recursion_tracker
  }

  /// Increases the token count by one.
  ///
  /// This should be called each time a token is processed.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let mut tracker = Tracker::new();
  /// tracker.increase_token();
  /// assert_eq!(tracker.token().tokens(), 1);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn increase_token(&mut self) {
    self.token_mut().increase();
  }

  /// Increases the recursion depth by one.
  ///
  /// This should be called when entering a recursive function.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let mut tracker = Tracker::new();
  /// tracker.increase_recursion();
  /// assert_eq!(tracker.recursion().depth(), 1);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn increase_recursion(&mut self) {
    self.recursion_mut().increase();
  }

  /// Decreases the recursion depth by one.
  ///
  /// This should be called when returning from a recursive function.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  ///
  /// let mut tracker = Tracker::new();
  /// tracker.increase_recursion();
  /// tracker.decrease_recursion();
  /// assert_eq!(tracker.recursion().depth(), 0);
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn decrease_recursion(&mut self) {
    self.recursion_mut().decrease();
  }

  /// Checks if any of the limits have been exceeded.
  ///
  /// Returns `Ok(())` if both limits are within bounds, or `Err(LimitExceeded)`
  /// if either the token count or recursion depth exceeds its configured maximum.
  ///
  /// The recursion limit is checked first, so if both limits are exceeded, you'll
  /// get a `LimitExceeded::Recursion` error.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::tracker::Tracker;
  /// use logosky::utils::token_tracker::TokenLimiter;
  ///
  /// let mut tracker = Tracker::with_token_tracker(
  ///     TokenLimiter::with_limitation(3)
  /// );
  ///
  /// tracker.increase_token();
  /// tracker.increase_token();
  /// assert!(tracker.check().is_ok());
  ///
  /// tracker.increase_token();
  /// tracker.increase_token(); // Exceeds limit
  /// assert!(tracker.check().is_err());
  /// ```
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub fn check(&self) -> Result<(), LimitExceeded> {
    self
      .recursion_tracker
      .check()
      .map_err(LimitExceeded::from)?;
    self.token_tracker.check().map_err(LimitExceeded::from)?;
    Ok(())
  }
}

impl State for Tracker {
  type Error = LimitExceeded;
}
