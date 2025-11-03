use crate::utils::{Expected, Span};

/// An error representing an unexpected token encountered during parsing.
///
/// This error type captures the location (span), what token was found (if any),
/// and what token(s) were expected. It's commonly used in parsers to provide
/// detailed error messages when the input doesn't match the expected syntax.
///
/// # Type Parameters
///
/// * `T` - The type of the actual token that was found
/// * `TK` - The type of the expected token (often an enum of token kinds)
///
/// # Examples
///
/// ```
/// use logosky::utils::{Expected, UnexpectedToken, Span};
///
/// // Error when expecting a specific token but got something else
/// let error = UnexpectedToken::with_found(
///     Span::new(10, 15),
///     "}",
///     Expected::one("{")
/// );
/// assert_eq!(error.span(), Span::new(10, 15));
/// assert_eq!(format!("{}", error), "unexpected token '}', expected '{'");
///
/// // Error when expecting one of multiple tokens
/// let error = UnexpectedToken::with_found(
///     Span::new(0, 10),
///     "identifier",
///     Expected::one_of(&["if", "while", "for"])
/// );
/// assert_eq!(
///     format!("{}", error),
///     "unexpected token 'identifier', expected one of: 'if', 'while', 'for'"
/// );
///
/// // Error when reaching end of input unexpectedly
/// let error: UnexpectedToken<&str, &str> = UnexpectedToken::expected_one(
///     Span::new(100, 100),
///     "}"
/// );
/// assert_eq!(format!("{}", error), "unexpected end of input, expected '}'");
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct UnexpectedToken<T, TK: 'static> {
  span: Span,
  found: Option<T>,
  expected: Expected<TK>,
}

impl<T, TK> UnexpectedToken<T, TK> {
  /// Creates an unexpected token error without a found token.
  ///
  /// This is useful when the parser reaches the end of input unexpectedly.
  /// The error will indicate "unexpected end of input" in its display message.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error: UnexpectedToken<&str, &str> = UnexpectedToken::new(
  ///     Span::new(100, 100),
  ///     Expected::one("}")
  /// );
  /// assert!(error.found().is_none());
  /// assert_eq!(error.span(), Span::new(100, 100));
  /// assert_eq!(format!("{}", error), "unexpected end of input, expected '}'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(span: Span, expected: Expected<TK>) -> Self {
    Self::maybe_found(span, None, expected)
  }

  /// Creates a new unexpected token error with a single expected token.
  ///
  /// This is a convenience method that combines `new` with `Expected::one`.
  /// The error has no found token, indicating the end of input was reached.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedToken, Span};
  ///
  /// let error: UnexpectedToken<&str, &str> = UnexpectedToken::expected_one(
  ///     Span::new(50, 50),
  ///     ";"
  /// );
  /// assert!(error.found().is_none());
  /// assert_eq!(format!("{}", error), "unexpected end of input, expected ';'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected_one(span: Span, expected: TK) -> Self {
    Self::new(span, Expected::one(expected))
  }

  /// Creates a new unexpected token error with multiple expected tokens.
  ///
  /// This is a convenience method that combines `new` with `Expected::one_of`.
  /// The error has no found token, indicating the end of input was reached.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedToken, Span};
  ///
  /// let error: UnexpectedToken<&str, &str> = UnexpectedToken::expected_one_of(
  ///     Span::new(25, 25),
  ///     &["+", "-", "*", "/"]
  /// );
  /// assert!(error.found().is_none());
  /// assert_eq!(
  ///     format!("{}", error),
  ///     "unexpected end of input, expected one of: '+', '-', '*', '/'"
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected_one_of(span: Span, expected: &'static [TK]) -> Self {
    Self::new(span, Expected::one_of(expected))
  }

  /// Creates a new unexpected token error with an optional found token.
  ///
  /// This is the most general constructor. When `found` is `None`, the error
  /// indicates the end of input was reached. When `found` is `Some`, it indicates
  /// an unexpected token was encountered.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// // With a found token
  /// let error = UnexpectedToken::maybe_found(
  ///     Span::new(10, 14),
  ///     Some("else"),
  ///     Expected::one("if")
  /// );
  /// assert_eq!(error.found(), Some(&"else"));
  /// assert_eq!(format!("{}", error), "unexpected token 'else', expected 'if'");
  ///
  /// // Without a found token (end of input)
  /// let error: UnexpectedToken<&str, &str> = UnexpectedToken::maybe_found(
  ///     Span::new(50, 50),
  ///     None,
  ///     Expected::one("if")
  /// );
  /// assert_eq!(error.found(), None);
  /// assert_eq!(format!("{}", error), "unexpected end of input, expected 'if'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn maybe_found(span: Span, found: Option<T>, expected: Expected<TK>) -> Self {
    Self {
      span,
      found,
      expected,
    }
  }

  /// Creates a new unexpected token error with a found token.
  ///
  /// This indicates that a specific token was encountered when a different
  /// token (or one of several alternative tokens) was expected.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error = UnexpectedToken::with_found(
  ///     Span::new(5, 10),
  ///     "class",
  ///     Expected::one("fn")
  /// );
  /// assert_eq!(error.found(), Some(&"class"));
  /// assert_eq!(format!("{}", error), "unexpected token 'class', expected 'fn'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_found(span: Span, found: T, expected: Expected<TK>) -> Self {
    Self::maybe_found(span, Some(found), expected)
  }

  /// Returns the span of the unexpected token.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error = UnexpectedToken::with_found(
  ///     Span::new(10, 15),
  ///     "identifier",
  ///     Expected::one("number")
  /// );
  /// assert_eq!(error.span(), Span::new(10, 15));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    self.span
  }

  /// Returns a reference to the found token, if any.
  ///
  /// Returns `None` if the error represents an unexpected end of input.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error = UnexpectedToken::with_found(
  ///     Span::new(0, 10),
  ///     "identifier",
  ///     Expected::one("number")
  /// );
  /// assert_eq!(error.found(), Some(&"identifier"));
  ///
  /// let eof_error: UnexpectedToken<&str, &str> = UnexpectedToken::expected_one(
  ///     Span::new(100, 100),
  ///     "}"
  /// );
  /// assert_eq!(eof_error.found(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn found(&self) -> Option<&T> {
    self.found.as_ref()
  }

  /// Returns a reference to the expected token(s).
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error = UnexpectedToken::with_found(
  ///     Span::new(5, 6),
  ///     "}",
  ///     Expected::one("{")
  /// );
  /// assert_eq!(*error.expected(), Expected::one("{"));
  /// if let Expected::One(value) = error.expected() {
  ///     assert_eq!(*value, "{");
  /// }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected(&self) -> &Expected<TK> {
    &self.expected
  }

  /// Bumps both the start and end positions of the span by the given offset.
  ///
  /// This is useful when adjusting error positions after processing or
  /// when combining spans from different contexts.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let mut error = UnexpectedToken::with_found(
  ///     Span::new(10, 15),
  ///     "}",
  ///     Expected::one("{")
  /// );
  /// error.bump(5);
  /// assert_eq!(error.span(), Span::new(15, 20));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn bump(&mut self, offset: usize) {
    self.span.bump_end(offset);
    self.span.bump_start(offset);
  }

  /// Consumes the error and returns its components.
  ///
  /// This method deconstructs the error into its constituent parts:
  /// the span, the found token (if any), and the expected token(s).
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedToken, Span};
  ///
  /// let error = UnexpectedToken::with_found(
  ///     Span::new(5, 6),
  ///     "}",
  ///     Expected::one("{")
  /// );
  /// let (span, found, expected) = error.into_components();
  /// assert_eq!(span, Span::new(5, 6));
  /// assert_eq!(found, Some("}"));
  /// assert_eq!(expected, Expected::one("{"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Span, Option<T>, Expected<TK>) {
    (self.span, self.found, self.expected)
  }
}

impl<T: core::fmt::Display, TK: core::fmt::Display + 'static> core::fmt::Display
  for UnexpectedToken<T, TK>
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.found {
      Some(found) => write!(f, "unexpected token '{found}', {}", self.expected),
      None => write!(f, "unexpected end of input, {}", self.expected),
    }
  }
}

impl<T: core::fmt::Debug + core::fmt::Display, TK: core::fmt::Display + core::fmt::Debug + 'static>
  core::error::Error for UnexpectedToken<T, TK>
{
}
