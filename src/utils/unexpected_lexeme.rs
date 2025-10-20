use derive_more::{From, IsVariant, TryUnwrap, Unwrap};

use super::{PositionedChar, Span};

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

impl<Char> Lexeme<Char> {
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
  #[inline]
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
  #[inline]
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
  #[inline]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        Span::from(pos..(pos + pc.char_ref().len()))
      }
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
  #[inline]
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

/// A zero-copy error structure combining an unexpected lexeme with a diagnostic hint.
///
/// `UnexpectedLexeme` pairs a [`Lexeme`] (identifying what went wrong) with a hint
/// (describing what was expected instead). This structure is designed for building
/// rich, informative error messages without allocating strings.
///
/// # Type Parameters
///
/// - **Char**: The character type (typically `char` for UTF-8 or `u8` for bytes)
/// - **Hint**: Any type describing what was expected (often implements `Display`)
///
/// # Design Philosophy
///
/// This type stores:
/// - The **lexeme** of the unexpected fragment ([`Char`](Lexeme::Char) or [`Span`](Lexeme::Span))
/// - A **hint** describing what was expected next (any type you choose)
///
/// The hint is left generic and unconstrained so you can carry:
/// - Simple strings: `&'static str`
/// - Token kinds: Your own `TokenKind` enum
/// - Rich structures: Custom diagnostic types with multiple suggestions
///
/// # Deref Behavior
///
/// `UnexpectedLexeme` implements `Deref` to `Lexeme<Char>`, so you can call all
/// `Lexeme` methods directly on an `UnexpectedLexeme` instance.
///
/// # Use Cases
///
/// - **Lexer errors**: Report unexpected characters with "expected" hints
/// - **Parser errors**: Track unexpected tokens with contextual information
/// - **Error recovery**: Store partial error info without allocating
/// - **Diagnostic tools**: Build structured error reports for IDEs
///
/// # Examples
///
/// ## Basic Error with String Hint
///
/// ```rust
/// use logosky::utils::{UnexpectedLexeme, PositionedChar};
///
/// let error = UnexpectedLexeme::from_char(
///     PositionedChar::with_position('!', 42),
///     "expected letter or digit"
/// );
///
/// assert!(error.is_char());
/// assert_eq!(error.lexeme().unwrap_char().position(), 42);
/// assert_eq!(*error.hint(), "expected letter or digit");
/// ```
///
/// ## With Token Kind Hint
///
/// ```rust,ignore
/// use logosky::utils::{UnexpectedLexeme, Span};
///
/// #[derive(Debug, Clone)]
/// enum Expected {
///     Token(TokenKind),
///     OneOf(Vec<TokenKind>),
/// }
///
/// let error = UnexpectedLexeme::from_span(
///     Span::new(10, 15),
///     Expected::OneOf(vec![TokenKind::Semicolon, TokenKind::Comma])
/// );
///
/// // Use in error display
/// match error.hint() {
///     Expected::Token(kind) => println!("Expected {:?}", kind),
///     Expected::OneOf(kinds) => println!("Expected one of: {:?}", kinds),
/// }
/// ```
///
/// ## Mapping Hints
///
/// ```rust
/// use logosky::utils::{UnexpectedLexeme, PositionedChar};
///
/// let error = UnexpectedLexeme::from_char(
///     PositionedChar::with_position('x', 5),
///     "number"
/// );
///
/// // Transform the hint to a more detailed message
/// let detailed = error.map_hint(|hint| format!("expected {}, found 'x'", hint));
///
/// assert_eq!(detailed.hint(), "expected number, found 'x'");
/// ```
///
/// ## Accessing Lexeme via Deref
///
/// ```rust
/// use logosky::utils::{UnexpectedLexeme, PositionedChar};
///
/// let error = UnexpectedLexeme::from_char(
///     PositionedChar::with_position('!', 10),
///     "identifier"
/// );
///
/// // Call Lexeme methods directly
/// assert!(error.is_char());
/// let span = error.span(); // Deref to Lexeme, call span()
/// assert_eq!(span.start(), 10);
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct UnexpectedLexeme<Char, Hint> {
  lexeme: Lexeme<Char>,
  hint: Hint,
}

impl<Char, Hint> core::ops::Deref for UnexpectedLexeme<Char, Hint> {
  type Target = Lexeme<Char>;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.lexeme
  }
}

impl<Char, Hint> core::ops::DerefMut for UnexpectedLexeme<Char, Hint> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.lexeme
  }
}

impl<Char, Hint> UnexpectedLexeme<Char, Hint> {
  /// Creates a new `UnexpectedLexeme` from a lexeme and hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, Lexeme, PositionedChar};
  ///
  /// let lexeme = Lexeme::from(PositionedChar::with_position('!', 5));
  /// let error = UnexpectedLexeme::new(lexeme, "identifier");
  ///
  /// assert_eq!(*error.hint(), "identifier");
  /// ```
  #[inline(always)]
  pub const fn new(lexeme: Lexeme<Char>, hint: Hint) -> Self {
    Self { lexeme, hint }
  }

  /// Constructs an error from a positioned character and hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('$', 42),
  ///     "alphanumeric character"
  /// );
  ///
  /// assert!(error.is_char());
  /// assert_eq!(error.unwrap_char().position(), 42);
  /// ```
  #[inline]
  pub const fn from_char(pc: PositionedChar<Char>, hint: Hint) -> Self {
    Self::new(Lexeme::Char(pc), hint)
  }

  /// Constructs an error from a byte span and hint (const version).
  ///
  /// Use this in const contexts where `Into<Span>` conversions aren't available.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, Span};
  ///
  /// let error: UnexpectedLexeme<char, _> = UnexpectedLexeme::from_span_const(
  ///     Span::new(10, 15),
  ///     "semicolon"
  /// );
  ///
  /// assert!(error.is_span());
  /// ```
  #[inline]
  pub const fn from_span_const(span: Span, hint: Hint) -> Self {
    Self::new(Lexeme::Span(span), hint)
  }

  /// Constructs an error from a byte span and hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::UnexpectedLexeme;
  ///
  /// let error: UnexpectedLexeme<char, _> = UnexpectedLexeme::from_span(10..15, "closing brace");
  ///
  /// assert!(error.is_span());
  /// assert_eq!(error.unwrap_span().start(), 10);
  /// ```
  #[inline]
  pub fn from_span(span: impl Into<Span>, hint: Hint) -> Self {
    Self::new(Lexeme::Span(span.into()), hint)
  }

  /// Returns a reference to the lexeme.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 5),
  ///     "digit"
  /// );
  ///
  /// assert!(error.lexeme().is_char());
  /// ```
  #[inline(always)]
  pub const fn lexeme(&self) -> &Lexeme<Char> {
    &self.lexeme
  }

  /// Returns a reference to the hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 5),
  ///     "expected digit"
  /// );
  ///
  /// assert_eq!(*error.hint(), "expected digit");
  /// ```
  #[inline(always)]
  pub const fn hint(&self) -> &Hint {
    &self.hint
  }

  /// Returns a mutable reference to the lexeme.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let mut error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 5),
  ///     "digit"
  /// );
  ///
  /// error.lexeme_mut().bump(10);
  /// assert_eq!(error.unwrap_char().position(), 15);
  /// ```
  #[inline(always)]
  pub const fn lexeme_mut(&mut self) -> &mut Lexeme<Char> {
    &mut self.lexeme
  }

  /// Returns a mutable reference to the hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let mut error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 5),
  ///     String::from("digit")
  /// );
  ///
  /// error.hint_mut().push_str(" or letter");
  /// assert_eq!(error.hint(), "digit or letter");
  /// ```
  #[inline(always)]
  pub const fn hint_mut(&mut self) -> &mut Hint {
    &mut self.hint
  }

  /// Consumes self and returns the lexeme and hint as a tuple.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('!', 10),
  ///     "identifier"
  /// );
  ///
  /// let (lexeme, hint) = error.into_components();
  /// assert!(lexeme.is_char());
  /// assert_eq!(hint, "identifier");
  /// ```
  #[inline]
  pub fn into_components(self) -> (Lexeme<Char>, Hint) {
    (self.lexeme, self.hint)
  }

  /// Consumes self and returns only the lexeme.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('!', 10),
  ///     "identifier"
  /// );
  ///
  /// let lexeme = error.into_lexeme();
  /// assert!(lexeme.is_char());
  /// ```
  #[inline]
  pub fn into_lexeme(self) -> Lexeme<Char> {
    self.lexeme
  }

  /// Consumes self and returns only the hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('!', 10),
  ///     "identifier"
  /// );
  ///
  /// let hint = error.into_hint();
  /// assert_eq!(hint, "identifier");
  /// ```
  #[inline]
  pub fn into_hint(self) -> Hint {
    self.hint
  }

  /// Returns the byte span covered by this lexeme using a custom length function.
  ///
  /// This delegates to [`Lexeme::span_with`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('€', 5),
  ///     "ASCII character"
  /// );
  ///
  /// let span = error.span_with(|c: &char| c.len_utf8());
  /// assert_eq!(span.start(), 5);
  /// assert_eq!(span.end(), 8); // '€' is 3 bytes
  /// ```
  #[inline]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Span {
    self.lexeme.span_with(len_of)
  }

  /// Returns the byte span covered by this lexeme.
  ///
  /// This delegates to [`Lexeme::span`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar, Span};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 10),
  ///     "digit"
  /// );
  ///
  /// assert_eq!(error.span(), Span::new(10, 11));
  /// ```
  #[inline]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    self.lexeme.span()
  }

  /// Maps the character type to another type, preserving the hint.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('a', 5),
  ///     "digit"
  /// );
  ///
  /// let upper = error.map_char(|c| c.to_ascii_uppercase());
  /// assert_eq!(upper.unwrap_char().char(), 'A');
  /// assert_eq!(*upper.hint(), "digit");
  /// ```
  #[inline]
  pub fn map_char<F, NewChar>(self, f: F) -> UnexpectedLexeme<NewChar, Hint>
  where
    F: FnMut(Char) -> NewChar,
  {
    UnexpectedLexeme {
      lexeme: self.lexeme.map(f),
      hint: self.hint,
    }
  }

  /// Maps the hint type to another type, preserving the lexeme.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('!', 5),
  ///     "digit"
  /// );
  ///
  /// let detailed = error.map_hint(|h| format!("expected {}", h));
  /// assert_eq!(detailed.hint(), "expected digit");
  /// ```
  #[inline]
  pub fn map_hint<F, NewHint>(self, f: F) -> UnexpectedLexeme<Char, NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedLexeme {
      lexeme: self.lexeme,
      hint: f(self.hint),
    }
  }

  /// Maps both the character and hint types to other types.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('a', 5),
  ///     "number"
  /// );
  ///
  /// let transformed = error.map(
  ///     |c| c.to_ascii_uppercase(),
  ///     |h| format!("expected {}", h)
  /// );
  ///
  /// assert_eq!(transformed.unwrap_char().char(), 'A');
  /// assert_eq!(transformed.hint(), "expected number");
  /// ```
  #[inline]
  pub fn map<F, NewChar, G, NewHint>(self, f: F, g: G) -> UnexpectedLexeme<NewChar, NewHint>
  where
    F: FnMut(Char) -> NewChar,
    G: FnOnce(Hint) -> NewHint,
  {
    UnexpectedLexeme {
      lexeme: self.lexeme.map(f),
      hint: g(self.hint),
    }
  }

  /// Adjusts the lexeme's position/span by adding `n` bytes.
  ///
  /// Returns a mutable reference to self for method chaining.
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedLexeme, PositionedChar};
  ///
  /// let mut error = UnexpectedLexeme::from_char(
  ///     PositionedChar::with_position('x', 5),
  ///     "digit"
  /// );
  ///
  /// error.bump(10);
  /// assert_eq!(error.unwrap_char().position(), 15);
  /// ```
  #[inline]
  pub const fn bump(&mut self, n: usize) -> &mut Self {
    self.lexeme.bump(n);
    self
  }
}

/// A trait for character-like types that can report their encoded length in bytes.
///
/// `CharLen` provides a uniform way to query the byte length of different character
/// types, which is essential for converting positioned characters into byte spans.
///
/// # Implementations
///
/// LogoSky provides implementations for:
/// - **`u8`**: Always returns `1` (single byte)
/// - **`char`**: Returns `len_utf8()` (1-4 bytes depending on the character)
/// - **`&T`**: Delegates to `T::len()` for any `T: CharLen`
///
/// # Design Note
///
/// This trait is **sealed** and cannot be implemented outside of LogoSky. If you need
/// to work with a custom character type, use [`Lexeme::span_with`] or
/// [`UnexpectedLexeme::span_with`] and provide your own length function.
///
/// # Use Cases
///
/// - **Span calculation**: Convert positioned characters to byte spans automatically
/// - **UTF-8 handling**: Properly account for multi-byte characters
/// - **Error reporting**: Determine the exact byte range of an unexpected character
///
/// # Examples
///
/// ## Automatic Length Detection
///
/// ```rust
/// use logosky::utils::{Lexeme, PositionedChar};
///
/// // ASCII character (1 byte)
/// let ascii = Lexeme::from(PositionedChar::with_position('a', 10));
/// let span = ascii.span();
/// assert_eq!(span.len(), 1);
///
/// // Multi-byte UTF-8 character (3 bytes)
/// let emoji = Lexeme::from(PositionedChar::with_position('€', 20));
/// let span = emoji.span();
/// assert_eq!(span.len(), 3);
/// ```
///
/// ## With Custom Length Function
///
/// ```rust
/// use logosky::utils::{Lexeme, PositionedChar};
///
/// // For types that don't implement CharLen, use span_with
/// struct CustomChar(char);
///
/// let lexeme = Lexeme::from(PositionedChar::with_position(CustomChar('€'), 5));
/// let span = lexeme.span_with(|c| c.0.len_utf8());
///
/// assert_eq!(span.start(), 5);
/// assert_eq!(span.end(), 8);
/// ```
#[allow(clippy::len_without_is_empty)]
pub trait CharLen: sealed::Sealed {
  /// Returns the length of this character in bytes.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::{Lexeme, PositionedChar};
  ///
  /// // The trait is used internally by span()
  /// let ascii = Lexeme::from(PositionedChar::with_position('A', 0));
  /// assert_eq!(ascii.span().len(), 1);
  ///
  /// let euro = Lexeme::from(PositionedChar::with_position('€', 0));
  /// assert_eq!(euro.span().len(), 3);
  ///
  /// let crab = Lexeme::from(PositionedChar::with_position('🦀', 0));
  /// assert_eq!(crab.span().len(), 4);
  /// ```
  fn len(&self) -> usize;
}

mod sealed {
  use super::CharLen;

  pub trait Sealed {}

  impl Sealed for u8 {}
  impl Sealed for char {}

  impl<T: Sealed> Sealed for &T {}

  impl CharLen for u8 {
    #[inline(always)]
    fn len(&self) -> usize {
      1
    }
  }

  impl CharLen for char {
    #[inline(always)]
    fn len(&self) -> usize {
      self.len_utf8()
    }
  }

  impl<T: CharLen> CharLen for &T {
    #[inline(always)]
    fn len(&self) -> usize {
      (*self).len()
    }
  }
}
