use derive_more::{Display, IsVariant};

use super::{CharLen, Lexeme, PositionedChar, Span};

/// An enumeration of line terminator types.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, IsVariant, Display)]
pub enum LineTerminator {
  /// A newline character (`\n`).
  #[display("\\n")]
  NewLine,
  /// A carriage return character (`\r`).
  #[display("\\r")]
  CarriageReturn,
  /// A carriage return followed by a newline (`\r\n`).
  #[display("\\r\\n")]
  CarriageReturnNewLine,
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

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref(&self) -> &Self::Target {
    &self.lexeme
  }
}

impl<Char, Hint> core::ops::DerefMut for UnexpectedLexeme<Char, Hint> {
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
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
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn bump(&mut self, n: usize) -> &mut Self {
    self.lexeme.bump(n);
    self
  }
}
