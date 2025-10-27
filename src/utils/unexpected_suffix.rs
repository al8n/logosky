use super::{Lexeme, PositionedChar, Span};

/// An error indicating that an unexpected suffix was found after a valid token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnexpectedSuffix<Char> {
  token: Span,
  suffix: Lexeme<Char>,
}

impl<Char> UnexpectedSuffix<Char> {
  /// Creates a new `UnexpectedSuffix` error with the span of the valid token and the unexpected suffix.
  ///
  /// ## Panics
  /// - If the suffix span starts before the token span ends.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::new(
  ///     Span::new(0, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(token: Span, suffix: Lexeme<Char>) -> Self {
    assert!(
      suffix.start() >= token.end(),
      "suffix starts before token ends"
    );

    Self { token, suffix }
  }

  /// Create a new `UnexpectedSuffix` error from the given token span and character with position.
  ///
  /// ## Panics
  /// - If the positioned character's position is before the token span ends.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::from_char(
  ///    Span::new(0, 5),
  ///    PositionedChar::with_position('x', 5)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn from_char(token: Span, ch: PositionedChar<Char>) -> Self {
    Self::new(token, Lexeme::Char(ch))
  }

  /// Create a new `UnexpectedSuffix` error from the given token span and the suffix span
  ///
  /// ## Panics
  /// - If the suffix span starts before the token span ends.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme};
  ///
  /// let error: UnexpectedSuffix<char> = UnexpectedSuffix::from_suffix(
  ///   Span::new(0, 5),
  ///   Span::new(5, 10)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn from_suffix(token: Span, span: Span) -> Self {
    Self::new(token, Lexeme::Span(span))
  }

  /// Returns the full span since the start of the valid token to the end of the unexpected suffix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::new(
  ///   Span::new(0, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// assert_eq!(error.span(), Span::new(0, 6));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span(&self) -> Span
  where
    Char: super::CharLen,
  {
    let start = self.token.start();
    let end = match &self.suffix {
      Lexeme::Char(positioned_char) => {
        positioned_char.position() + positioned_char.char_ref().char_len()
      }
      Lexeme::Span(span) => span.end(),
    };
    Span::new(start, end)
  }

  /// Returns the span of the valid token before the unexpected suffix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::new(
  ///     Span::new(0, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// assert_eq!(error.token(), Span::new(0, 5));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn token(&self) -> Span {
    self.token
  }

  /// Returns the unexpected suffix found after the valid token.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::new(
  ///    Span::new(0, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  ///
  /// assert_eq!(
  ///   error.suffix(),
  ///   &Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn suffix(&self) -> &Lexeme<Char> {
    &self.suffix
  }

  /// Consumes the error and returns the unexpected suffix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedSuffix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedSuffix::new(
  ///   Span::new(0, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// let (token, suffix) = error.into_components();
  /// assert_eq!(token, Span::new(0, 5));
  /// assert_eq!(
  ///   suffix,
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Span, Lexeme<Char>) {
    (self.token, self.suffix)
  }
}

impl<Char> core::fmt::Display for UnexpectedSuffix<Char>
where
  Char: super::human_display::DisplayHuman,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.suffix {
      Lexeme::Char(positioned_char) => {
        write!(
          f,
          "unexpected suffix '{}' at position {} found after {}",
          positioned_char.char_ref().display(),
          positioned_char.position(),
          self.token
        )
      }
      Lexeme::Span(span) => {
        write!(
          f,
          "unexpected suffix at {} found after {}",
          span, self.token
        )
      }
    }
  }
}

impl<Char> core::error::Error for UnexpectedSuffix<Char> where
  Char: super::human_display::DisplayHuman + core::fmt::Debug
{
}
