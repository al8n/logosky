/// A character paired with its byte position in the source input.
///
/// `PositionedChar` combines a character (or character-like value) with the byte offset
/// where it appears in the source. This is particularly useful for:
///
/// - **Error reporting**: Show exactly where an unexpected character occurred
/// - **Lexer state**: Track position while processing character-by-character
/// - **Diagnostics**: Build precise error messages with column/line information
/// - **Character-level parsing**: When token-level parsing is too coarse
///
/// # Type Parameter
///
/// - `Char`: The character type, typically `char` for UTF-8 text or `u8` for bytes
///
/// # Design
///
/// This type is designed to be lightweight and efficient:
/// - **Copy**: Can be freely copied (when `Char` is `Copy`)
/// - **Small**: Just the character plus one `usize` for position
/// - **Comparable**: Supports comparison operations based on both character and position
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use logosky::utils::PositionedChar;
///
/// let ch = PositionedChar::with_position('x', 42);
///
/// assert_eq!(ch.char(), 'x');
/// assert_eq!(ch.position(), 42);
/// ```
///
/// ## Character-by-Character Processing
///
/// ```rust,ignore
/// use logosky::utils::PositionedChar;
///
/// fn process_input(input: &str) -> Vec<PositionedChar<char>> {
///     input.char_indices()
///         .map(|(pos, ch)| PositionedChar::with_position(ch, pos))
///         .collect()
/// }
///
/// let positioned = process_input("hello");
/// assert_eq!(positioned[0].char(), 'h');
/// assert_eq!(positioned[0].position(), 0);
/// ```
///
/// ## Error Reporting
///
/// ```rust,ignore
/// use logosky::utils::PositionedChar;
///
/// fn report_unexpected(pc: PositionedChar<char>, input: &str) {
///     let line_start = input[..pc.position()]
///         .rfind('\n')
///         .map(|p| p + 1)
///         .unwrap_or(0);
///
///     let column = pc.position() - line_start;
///
///     eprintln!("Unexpected character '{}' at position {} (column {})",
///         pc.char(), pc.position(), column);
/// }
/// ```
///
/// ## Mapping Characters
///
/// ```rust
/// use logosky::utils::PositionedChar;
///
/// let lowercase = PositionedChar::with_position('a', 10);
/// let uppercase = lowercase.map(|c| c.to_ascii_uppercase());
///
/// assert_eq!(uppercase.char(), 'A');
/// assert_eq!(uppercase.position(), 10); // Position preserved
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PositionedChar<Char> {
  char: Char,
  position: usize,
}

impl<Char> PositionedChar<Char> {
  /// Create a new positioned character with position 0.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn new(char: Char) -> Self {
    Self::with_position(char, 0)
  }

  /// Create a new positioned character with the given position.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn with_position(char: Char, position: usize) -> Self {
    Self { char, position }
  }

  /// Get the character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn char(&self) -> Char
  where
    Char: Copy,
  {
    self.char
  }

  /// Get the reference to the character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn char_ref(&self) -> &Char {
    &self.char
  }

  /// Get a mutable reference to the character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn char_mut(&mut self) -> &mut Char {
    &mut self.char
  }

  /// Get the position.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn position(&self) -> usize {
    self.position
  }

  /// Set the position, returning a mutable reference of the positioned character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn set_position(&mut self, position: usize) -> &mut Self {
    self.position = position;
    self
  }

  /// Bump the position by `n`,  returning a mutable reference of the positioned character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn bump_position(&mut self, n: usize) -> &mut Self {
    self.position += n;
    self
  }

  /// Converts the positioned character to a reference.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn as_ref(&self) -> PositionedChar<&Char> {
    PositionedChar {
      char: &self.char,
      position: self.position,
    }
  }

  /// Converts the positioned character to a mutable reference.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub const fn as_mut(&mut self) -> PositionedChar<&mut Char> {
    PositionedChar {
      char: &mut self.char,
      position: self.position,
    }
  }

  /// Maps the character to another character, returning a new positioned character.
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
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
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  pub fn into_components(self) -> (Char, usize) {
    (self.char, self.position)
  }
}

impl<Char: core::fmt::Display> core::fmt::Display for PositionedChar<Char> {
  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.char)
  }
}
