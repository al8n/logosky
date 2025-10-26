
use super::Span;

/// Unclosed delimiter information.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Unclosed<Delimiter> {
  span: Span,
  delimiter: Delimiter,
}

impl<Delimiter> core::fmt::Display for Unclosed<Delimiter>
where
  Delimiter: core::fmt::Display,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "unclosed delimiter '{}'",
      self.delimiter
    )
  }
}

impl<Delimiter> core::error::Error for Unclosed<Delimiter>
where
  Delimiter: core::fmt::Display + core::fmt::Debug,
{
}

impl<Delimiter> Unclosed<Delimiter> {
  /// Creates a new `Unclosed` instance.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{Unclosed, Span};
  ///
  /// let unclosed = Unclosed::new(Span::new(5, 10), '(');
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(span: Span, delimiter: Delimiter) -> Self {
    Self { span, delimiter }
  }

  /// Returns the span of the unclosed delimiter.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{Unclosed, Span};
  ///
  /// let unclosed = Unclosed::new(Span::new(5, 10), '(');
  /// assert_eq!(unclosed.span(), Span::new(5, 10));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    self.span
  }

  /// Returns a reference to the unclosed delimiter.
  /// 
  /// ## Examples
  /// 
  /// ```rust
  /// use logosky::utils::{Unclosed, Span};
  /// 
  /// let unclosed = Unclosed::new(Span::new(5, 10), '{');
  /// assert_eq!(unclosed.delimiter_ref(), &'{');
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn delimiter_ref(&self) -> &Delimiter {
    &self.delimiter
  }

  /// Returns the unclosed delimiter.
  /// 
  /// ## Examples
  /// 
  /// ```rust
  /// use logosky::utils::{Unclosed, Span};
  /// 
  /// let unclosed = Unclosed::new(Span::new(5, 10), '[');
  /// assert_eq!(unclosed.delimiter(), '[');
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn delimiter(&mut self) -> Delimiter
  where
    Delimiter: Copy,
  {
    self.delimiter
  }
}
