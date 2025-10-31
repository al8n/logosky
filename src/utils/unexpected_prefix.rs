use super::{Lexeme, PositionedChar, Span};

/// An error indicating that an unexpected prefix was found after a valid token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnexpectedPrefix<Char, Knowledge> {
  token: Span,
  prefix: Lexeme<Char>,
  knowledge: Option<Knowledge>,
}

impl<Char, Knowledge> UnexpectedPrefix<Char, Knowledge> {
  /// Creates a new `UnexpectedPrefix` error with the span of the valid token and the unexpected prefix.
  ///
  /// ## Panics
  /// - If the prefix span ends after the token span starts.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::new(
  ///     Span::new(0, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(token: Span, prefix: Lexeme<Char>) -> Self
  where
    Char: super::CharLen,
  {
    assert!(
      prefix.end() <= token.start(),
      "prefix ends after token starts"
    );

    Self {
      token,
      prefix,
      knowledge: None,
    }
  }

  /// Create a new `UnexpectedPrefix` error from the given token span and character with position.
  ///
  /// ## Panics
  /// - If the positioned character's position is before the token span ends.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::from_char(
  ///    Span::new(0, 5),
  ///    PositionedChar::with_position('x', 5)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn from_char(token: Span, ch: PositionedChar<Char>) -> Self
  where
    Char: super::CharLen,
  {
    Self::new(token, Lexeme::Char(ch))
  }

  /// Adds knowledge to the `UnexpectedPrefix` error.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_knowledge_const(mut self, knowledge: Knowledge) -> Self
  where
    Knowledge: Copy,
  {
    self.knowledge = Some(knowledge);
    self
  }

  /// Adds knowledge to the `UnexpectedPrefix` error.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn with_knowledge(mut self, knowledge: Knowledge) -> Self {
    self.knowledge = Some(knowledge);
    self
  }

  /// Create a new `UnexpectedPrefix` error from the given token span and the prefix span
  ///
  /// ## Panics
  /// - If the prefix span starts before the token span ends.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme};
  ///
  /// let error: UnexpectedPrefix<char> = UnexpectedPrefix::from_prefix(
  ///   Span::new(0, 5),
  ///   Span::new(5, 10)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn from_prefix(token: Span, span: Span) -> Self
  where
    Char: super::CharLen,
  {
    Self::new(token, Lexeme::Span(span))
  }

  /// Returns the full span since the start of the valid token to the end of the unexpected prefix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::new(
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
    let end = match &self.prefix {
      Lexeme::Char(positioned_char) => {
        positioned_char.position() + positioned_char.char_ref().char_len()
      }
      Lexeme::Span(span) => span.end(),
    };
    Span::new(start, end)
  }

  /// Returns the span of the valid token before the unexpected prefix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::new(
  ///     Span::new(0, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// assert_eq!(error.token(), Span::new(0, 5));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn token(&self) -> Span {
    self.token
  }

  /// Returns the unexpected prefix found before the valid token.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::new(
  ///    Span::new(0, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  ///
  /// assert_eq!(
  ///   error.prefix(),
  ///   &Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn prefix(&self) -> &Lexeme<Char> {
    &self.prefix
  }

  /// Consumes the error and returns the unexpected prefix.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error = UnexpectedPrefix::new(
  ///   Span::new(0, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// let (token, prefix) = error.into_components();
  /// assert_eq!(token, Span::new(0, 5));
  /// assert_eq!(
  ///   prefix,
  ///   Lexeme::Char(PositionedChar::with_position('x', 5))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Span, Lexeme<Char>) {
    (self.token, self.prefix)
  }
}

impl<Char, Knowledge> core::fmt::Display for UnexpectedPrefix<Char, Knowledge>
where
  Char: super::human_display::DisplayHuman,
  Knowledge: super::human_display::DisplayHuman,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.prefix {
      Lexeme::Char(positioned_char) => match &self.knowledge {
        None => write!(
          f,
          "unexpected prefix '{}' at position {} found before {}",
          positioned_char.char_ref().display(),
          positioned_char.position(),
          self.token
        ),
        Some(knowledge) => {
          write!(
            f,
            "unexpected prefix '{}' at position {} found before '{}'@({})",
            positioned_char.char_ref().display(),
            positioned_char.position(),
            knowledge.display(),
            self.token
          )
        }
      },
      Lexeme::Span(span) => match &self.knowledge {
        Some(knowledge) => write!(
          f,
          "unexpected prefix at {} found before '{}'@({})",
          span,
          knowledge.display(),
          self.token
        ),
        None => write!(
          f,
          "unexpected prefix at {} found before {}",
          span, self.token
        ),
      },
    }
  }
}

impl<Char, Knowledge> core::error::Error for UnexpectedPrefix<Char, Knowledge>
where
  Char: super::human_display::DisplayHuman + core::fmt::Debug,
  Knowledge: super::human_display::DisplayHuman + core::fmt::Debug,
{
}
