/// A positioned character.
///
/// Which contains the character and its position in the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PositionedChar<Char> {
  char: Char,
  position: usize,
}

impl<Char> PositionedChar<Char> {
  /// Create a new positioned character with position 0.
  #[inline]
  pub const fn new(char: Char) -> Self {
    Self::with_position(char, 0)
  }

  /// Create a new positioned character with the given position.
  #[inline]
  pub const fn with_position(char: Char, position: usize) -> Self {
    Self { char, position }
  }

  /// Get the character.
  #[inline]
  pub const fn char(&self) -> &Char {
    &self.char
  }

  /// Get the position.
  #[inline]
  pub const fn position(&self) -> usize {
    self.position
  }

  /// Set the position, returning a new positioned character.
  #[inline]
  pub const fn set_position(&mut self, position: usize) -> &mut Self {
    self.position = position;
    self
  }

  /// Converts the positioned character to a reference.
  #[inline]
  pub const fn as_ref(&self) -> PositionedChar<&Char> {
    PositionedChar {
      char: &self.char,
      position: self.position,
    }
  }

  /// Converts the positioned character to a mutable reference.
  #[inline]
  pub const fn as_mut(&mut self) -> PositionedChar<&mut Char> {
    PositionedChar {
      char: &mut self.char,
      position: self.position,
    }
  }

  /// Maps the character to another character, returning a new positioned character.
  #[inline]
  pub fn map<NewChar, F>(self, f: F) -> PositionedChar<NewChar>
  where
    F: FnOnce(Char) -> NewChar,
  {
    PositionedChar {
      char: f(self.char),
      position: self.position,
    }
  }

  /// Consumes the positioned character, returning the character and its position.
  #[inline]
  pub fn into_components(self) -> (Char, usize) {
    (self.char, self.position)
  }
}

impl<Char: core::fmt::Display> core::fmt::Display for PositionedChar<Char> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.char)
  }
}
