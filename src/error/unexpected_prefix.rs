use crate::utils::{CharLen, Lexeme, PositionedChar, Span, human_display::DisplayHuman};

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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///     Span::new(1, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(token: Span, prefix: Lexeme<Char>) -> Self
  where
    Char: CharLen,
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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::from_char(
  ///    Span::new(1, 5),
  ///    PositionedChar::with_position('x', 0)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn from_char(token: Span, ch: PositionedChar<Char>) -> Self
  where
    Char: CharLen,
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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::from_prefix(
  ///   Span::new(6, 10),
  ///   Span::new(0, 6)
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn from_prefix(token: Span, span: Span) -> Self
  where
    Char: CharLen,
  {
    Self::new(token, Lexeme::Span(span))
  }

  /// Returns the full span since the start of the unexpected prefix to the end of the valid token.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///   Span::new(1, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// assert_eq!(error.span(), Span::new(0, 5));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    let end = self.token.end();
    let start = match &self.prefix {
      Lexeme::Char(positioned_char) => positioned_char.position(),
      Lexeme::Span(span) => span.start(),
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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///     Span::new(1, 5),
  ///     Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// assert_eq!(error.token(), Span::new(1, 5));
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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///    Span::new(1, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  ///
  /// assert_eq!(
  ///   error.prefix(),
  ///   &Lexeme::Char(PositionedChar::with_position('x', 0))
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
  /// let error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///   Span::new(1, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// let (token, prefix) = error.into_components();
  /// assert_eq!(token, Span::new(1, 5));
  /// assert_eq!(
  ///   prefix,
  ///   Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Span, Lexeme<Char>) {
    (self.token, self.prefix)
  }

  /// Bumps both the start and end positions of the token span by the given offset.
  ///
  /// This is useful when adjusting error positions after processing or
  /// when combining spans from different contexts.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedPrefix, Span, Lexeme, PositionedChar};
  ///
  /// let mut error: UnexpectedPrefix<char, ()> = UnexpectedPrefix::new(
  ///   Span::new(1, 5),
  ///   Lexeme::Char(PositionedChar::with_position('x', 0))
  /// );
  /// error.bump(10);
  /// assert_eq!(error.token(), Span::new(11, 15));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn bump(&mut self, offset: usize) {
    self.token.bump(offset);
  }
}

impl<Char, Knowledge> core::fmt::Display for UnexpectedPrefix<Char, Knowledge>
where
  Char: DisplayHuman,
  Knowledge: DisplayHuman,
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
  Char: DisplayHuman + core::fmt::Debug,
  Knowledge: DisplayHuman + core::fmt::Debug,
{
}
