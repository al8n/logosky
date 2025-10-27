use derive_more::{From, IsVariant, TryUnwrap, Unwrap};

use super::{CharLen, PositionedChar, Span};

/// A compact, zero-copy description of a lexeme in source code.
///
/// `Lexeme` is a space-efficient way to represent either a single character or
/// a span of bytes from the original source. It **does not own text** - instead
/// it carries just enough information to identify the lexeme's location.
///
/// # Variants
///
/// - **Char**: A single positioned character (e.g., an unexpected '`{`' at position 42)
/// - **Span**: A byte range into the source (e.g., an unexpected keyword spanning bytes 100-105)
///
/// # Design Philosophy
///
/// This type is designed for error reporting where you need to identify problematic
/// source locations without allocating strings. By storing only positions/ranges,
/// you can defer string slicing until error display time, keeping errors lightweight.
///
/// # Derived Helpers
///
/// This type provides several helper methods via derive macros:
/// - `is_char()` / `is_span()`: Check which variant it is
/// - `unwrap_char()` / `unwrap_span()`: Extract the inner value (panics if wrong variant)
/// - `try_unwrap_char()` / `try_unwrap_span()`: Try to extract the inner value
///
/// # Use Cases
///
/// - **Error reporting**: Identify unexpected tokens without copying text
/// - **Lexer errors**: Report malformed tokens with precise locations
/// - **Parser errors**: Track problematic syntax fragments
/// - **Diagnostic tools**: Build rich error messages with source context
///
/// # Examples
///
/// ## Single Character Lexeme
///
/// ```rust
/// use logosky::utils::{Lexeme, PositionedChar};
///
/// let pc = PositionedChar::with_position('!', 42);
/// let lexeme = Lexeme::from(pc);
///
/// assert!(lexeme.is_char());
/// assert_eq!(lexeme.unwrap_char().char(), '!');
/// assert_eq!(lexeme.unwrap_char().position(), 42);
/// ```
///
/// ## Span Lexeme
///
/// ```rust
/// use logosky::utils::{Lexeme, Span};
///
/// let span = Span::new(10, 15); // bytes 10-15
/// let lexeme: Lexeme<char> = Lexeme::from(span);
///
/// assert!(lexeme.is_span());
/// assert_eq!(lexeme.unwrap_span().start(), 10);
/// assert_eq!(lexeme.unwrap_span().end(), 15);
/// ```
///
/// ## Getting Span from Either Variant
///
/// ```rust
/// use logosky::utils::{Lexeme, PositionedChar};
///
/// let lexeme = Lexeme::from(PositionedChar::with_position('x', 5));
///
/// // 'x' is 1 byte in UTF-8
/// let span = lexeme.span();
/// assert_eq!(span.start(), 5);
/// assert_eq!(span.end(), 6);
/// ```
///
/// ## Mapping Characters
///
/// ```rust
/// use logosky::utils::{Lexeme, PositionedChar};
///
/// let lexeme = Lexeme::from(PositionedChar::with_position('a', 10));
/// let upper = lexeme.map(|c| c.to_ascii_uppercase());
///
/// assert_eq!(upper.unwrap_char().char(), 'A');
/// assert_eq!(upper.unwrap_char().position(), 10); // Position preserved
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, From)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Lexeme<Char> {
  /// A single positioned character with its byte position.
  ///
  /// Use this variant when the unexpected lexeme is exactly one character long.
  Char(PositionedChar<Char>),

  /// A half-open byte range `[start, end)` into the original source.
  ///
  /// The range must be non-empty (`start < end`) and point into the same
  /// buffer that was tokenized. Prefer UTF-8 boundary indices if you plan to
  /// slice `&str`.
  ///
  /// Use this variant when the unexpected lexeme spans multiple characters
  /// or when you want to represent a multi-byte token.
  Span(Span),
}

impl<Char> core::fmt::Display for Lexeme<Char>
where
  Char: super::human_display::DisplayHuman,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Char(pc) => write!(f, "'{}' at {}", pc.char_ref().display(), pc.position()),
      Self::Span(span) => write!(f, "{}", span),
    }
  }
}

impl<Char> Lexeme<Char> {
  /// Returns the start position of the lexeme.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar, Span};
  ///
  /// let char_lexeme = Lexeme::from(PositionedChar::with_position('x', 5));
  /// assert_eq!(char_lexeme.start(), 5);
  ///
  /// let span_lexeme: Lexeme<char> = Lexeme::from(Span::new(10, 15));
  /// assert_eq!(span_lexeme.start(), 10);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn start(&self) -> usize {
    match self {
      Self::Char(pc) => pc.position(),
      Self::Span(r) => r.start(),
    }
  }

  /// Returns the end position of the lexeme.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar, Span};
  ///
  /// let char_lexeme = Lexeme::from(PositionedChar::with_position('x', 5));
  /// assert_eq!(char_lexeme.end(), 6);
  ///
  /// let span_lexeme: Lexeme<char> = Lexeme::from(Span::new(10, 15));
  /// assert_eq!(span_lexeme.end(), 15);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn end(&self) -> usize
  where
    Char: CharLen,
  {
    match self {
      Self::Char(pc) => pc.position() + pc.char_ref().char_len(),
      Self::Span(r) => r.end(),
    }
  }

  /// Maps the character type to another type if this is a [`Char`](Lexeme::Char) variant.
  ///
  /// The [`Span`](Lexeme::Span) variant is left unchanged, as it doesn't contain
  /// a character value.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar};
  ///
  /// let lexeme = Lexeme::from(PositionedChar::with_position('a', 5));
  /// let upper = lexeme.map(|c| c.to_ascii_uppercase());
  ///
  /// assert_eq!(upper.unwrap_char().char(), 'A');
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn map<F, NewChar>(self, f: F) -> Lexeme<NewChar>
  where
    F: FnOnce(Char) -> NewChar,
  {
    match self {
      Self::Char(pc) => Lexeme::Char(pc.map(f)),
      Self::Span(r) => Lexeme::Span(r),
    }
  }

  /// Returns the byte span covered by this lexeme using a custom length function.
  ///
  /// For the [`Char`](Lexeme::Char) variant, the provided `len_of` function is
  /// called to determine how many bytes the character occupies. For the
  /// [`Span`](Lexeme::Span) variant, the span is returned directly.
  ///
  /// Use this method when your `Char` type doesn't implement [`CharLen`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar};
  ///
  /// let lexeme = Lexeme::from(PositionedChar::with_position('€', 10));
  ///
  /// // '€' is 3 bytes in UTF-8
  /// let span = lexeme.span_with(|c: &char| c.len_utf8());
  /// assert_eq!(span.start(), 10);
  /// assert_eq!(span.end(), 13);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Span {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        Span::from(pos..(pos + len_of(pc.char_ref())))
      }
      Self::Span(r) => *r,
    }
  }

  /// Returns the byte span covered by this lexeme.
  ///
  /// For the [`Char`](Lexeme::Char) variant, uses the [`CharLen`] trait to
  /// determine how many bytes the character occupies. For the [`Span`](Lexeme::Span)
  /// variant, returns the span directly.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar, Span};
  ///
  /// // Single character
  /// let char_lexeme = Lexeme::from(PositionedChar::with_position('x', 5));
  /// assert_eq!(char_lexeme.span(), Span::new(5, 6));
  ///
  /// // Span
  /// let span_lexeme: Lexeme<char> = Lexeme::from(Span::new(10, 15));
  /// assert_eq!(span_lexeme.span(), Span::new(10, 15));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    match self {
      Self::Char(pc) => pc.span(),
      Self::Span(r) => *r,
    }
  }

  /// Adjusts the position/span by adding `n` bytes to the offset.
  ///
  /// For the [`Char`](Lexeme::Char) variant, bumps the character's position.
  /// For the [`Span`](Lexeme::Span) variant, bumps both start and end of the span.
  ///
  /// Returns a mutable reference to self for method chaining.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar};
  ///
  /// let mut lexeme = Lexeme::from(PositionedChar::with_position('x', 5));
  /// lexeme.bump(10);
  ///
  /// assert_eq!(lexeme.unwrap_char().position(), 15);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn bump(&mut self, n: usize) -> &mut Self {
    match self {
      Self::Char(positioned_char) => {
        positioned_char.bump_position(n);
      }
      Self::Span(span) => {
        span.bump_span(n);
      }
    }

    self
  }
}
