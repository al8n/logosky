use crate::utils::{Expected, Span};

/// An error representing an unexpected keyword encountered during parsing.
///
/// This error type is specifically designed for keyword-based parsing where the
/// expected values are known string literals (keywords). Unlike `UnexpectedToken`,
/// this type always has a found value and the expected values are always static strings.
///
/// # Type Parameters
///
/// * `S` - The type representing the found keyword (often `String` or `&str`)
///
/// # Examples
///
/// ```
/// use logosky::utils::{Expected, UnexpectedKeyword, Span};
///
/// // Error when expecting a specific keyword
/// let error = UnexpectedKeyword::expected_one(
///     Span::new(10, 16),
///     "return",
///     "fn"
/// );
/// assert_eq!(error.found(), &"return");
/// assert_eq!(error.span(), Span::new(10, 16));
/// assert_eq!(format!("{}", error), "unexpected keyword 'return', expected 'fn'");
///
/// // Error when expecting one of multiple keywords
/// let error = UnexpectedKeyword::expected_one_of(
///     Span::new(0, 5),
///     "class",
///     &["struct", "enum", "trait"]
/// );
/// assert_eq!(
///     format!("{}", error),
///     "unexpected keyword 'class', expected one of: 'struct', 'enum', 'trait'"
/// );
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct UnexpectedKeyword<S> {
  span: Span,
  found: S,
  expected: Expected<&'static str>,
}

impl<S> UnexpectedKeyword<S> {
  /// Creates a new unexpected keyword error.
  ///
  /// This is the most general constructor that accepts the span, the found keyword,
  /// and the expected keyword(s) wrapped in an `Expected` enum.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::new(
  ///     Span::new(5, 8),
  ///     "let",
  ///     Expected::one("const")
  /// );
  /// assert_eq!(error.found(), &"let");
  /// assert_eq!(error.span(), Span::new(5, 8));
  /// assert_eq!(format!("{}", error), "unexpected keyword 'let', expected 'const'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(span: Span, found: S, expected: Expected<&'static str>) -> Self {
    Self {
      span,
      found,
      expected,
    }
  }

  /// Creates a new unexpected keyword error with a single expected keyword.
  ///
  /// This is a convenience method that combines `new` with `Expected::one`.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::expected_one(
  ///     Span::new(0, 3),
  ///     "var",
  ///     "let"
  /// );
  /// assert_eq!(error.found(), &"var");
  /// assert_eq!(format!("{}", error), "unexpected keyword 'var', expected 'let'");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected_one(span: Span, found: S, expected: &'static str) -> Self {
    Self::new(span, found, Expected::one(expected))
  }

  /// Creates a new unexpected keyword error with multiple expected keywords.
  ///
  /// This is a convenience method that combines `new` with `Expected::one_of`.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::expected_one_of(
  ///     Span::new(10, 18),
  ///     "function",
  ///     &["fn", "async", "const"]
  /// );
  /// assert_eq!(error.found(), &"function");
  /// assert_eq!(
  ///     format!("{}", error),
  ///     "unexpected keyword 'function', expected one of: 'fn', 'async', 'const'"
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected_one_of(span: Span, found: S, expected: &'static [&'static str]) -> Self {
    Self::new(span, found, Expected::one_of(expected))
  }

  /// Returns the span of the unexpected keyword.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::expected_one(
  ///     Span::new(20, 26),
  ///     "import",
  ///     "use"
  /// );
  /// assert_eq!(error.span(), Span::new(20, 26));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    self.span
  }

  /// Returns a reference to the found keyword.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::expected_one(
  ///     Span::new(0, 6),
  ///     "import",
  ///     "use"
  /// );
  /// assert_eq!(error.found(), &"import");
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn found(&self) -> &S {
    &self.found
  }

  /// Returns the expected keyword(s).
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{Expected, UnexpectedKeyword, Span};
  ///
  /// let error = UnexpectedKeyword::expected_one(
  ///     Span::new(5, 11),
  ///     "export",
  ///     "pub"
  /// );
  /// assert_eq!(error.expected(), Expected::one("pub"));
  /// if let Expected::One(keyword) = error.expected() {
  ///     assert_eq!(keyword, "pub");
  /// }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn expected(&self) -> Expected<&'static str> {
    self.expected
  }

  /// Bumps both the start and end positions of the span by the given offset.
  ///
  /// This is useful when adjusting error positions after processing or
  /// when combining spans from different contexts.
  ///
  /// # Examples
  ///
  /// ```
  /// use logosky::utils::{UnexpectedKeyword, Span};
  ///
  /// let mut error = UnexpectedKeyword::expected_one(
  ///     Span::new(10, 13),
  ///     "var",
  ///     "let"
  /// );
  /// error.bump(5);
  /// assert_eq!(error.span(), Span::new(15, 18));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn bump(&mut self, offset: usize) {
    self.span.bump_end(offset);
    self.span.bump_start(offset);
  }
}

impl<S: core::fmt::Display> core::fmt::Display for UnexpectedKeyword<S> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "unexpected keyword '{}', {}", self.found, self.expected)
  }
}

impl<S: core::fmt::Debug + core::fmt::Display> core::error::Error for UnexpectedKeyword<S> {}
