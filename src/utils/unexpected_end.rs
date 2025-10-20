use derive_more::Display;

#[cfg(not(any(feature = "std", feature = "alloc")))]
type Message = &'static str;

#[cfg(any(feature = "std", feature = "alloc"))]
type Message = std::borrow::Cow<'static, str>;

struct Inner;

impl Inner {
  #[cfg(not(any(feature = "std", feature = "alloc")))]
  const fn const_new(msg: &'static str) -> Message {
    msg
  }

  #[cfg(any(feature = "std", feature = "alloc"))]
  const fn const_new(msg: &'static str) -> Message {
    std::borrow::Cow::Borrowed(msg)
  }
}

/// A zero-sized marker indicating the parser expected more bytes when the file ended.
///
/// This hint type is used with [`UnexpectedEnd`] to create natural-reading error messages
/// like: `"unexpected end of file, expected byte"`.
///
/// # Use Case
///
/// Use `FileHint` when lexing byte-oriented input (files, byte streams) and you reach EOF
/// unexpectedly.
///
/// # Example
///
/// ```rust
/// use logosky::utils::{UnexpectedEnd, FileHint};
///
/// let error = UnexpectedEnd::EOF;
/// assert_eq!(error.to_string(), "unexpected end of file, expected byte");
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("byte")]
pub struct FileHint;

/// A zero-sized marker indicating the parser expected more tokens when the stream ended.
///
/// This hint type is used with [`UnexpectedEnd`] to create natural-reading error messages
/// like: `"unexpected end of token stream, expected token"`.
///
/// # Use Case
///
/// Use `TokenHint` when parsing a token stream with Chumsky and you reach end-of-tokens
/// unexpectedly.
///
/// # Example
///
/// ```rust
/// use logosky::utils::{UnexpectedEnd, TokenHint};
///
/// let error = UnexpectedEnd::EOT;
/// assert_eq!(error.to_string(), "unexpected end of token stream, expected token");
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("token")]
pub struct TokenHint;

/// A zero-sized marker indicating the parser expected more characters when the string ended.
///
/// This hint type is used with [`UnexpectedEnd`] to create natural-reading error messages
/// like: `"unexpected end of string, expected character"`.
///
/// # Use Case
///
/// Use `CharacterHint` when parsing character-by-character and you reach end-of-string
/// unexpectedly.
///
/// # Example
///
/// ```rust
/// use logosky::utils::{UnexpectedEnd, CharacterHint};
///
/// let error = UnexpectedEnd::EOS;
/// assert_eq!(error.to_string(), "unexpected end of string, expected character");
/// ```
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("character")]
pub struct CharacterHint;

/// A zero-copy, composable error type for unexpected end-of-input conditions.
///
/// `UnexpectedEnd` represents situations where the parser or lexer expected more input
/// but encountered the end of the stream instead (EOF, EOT, EOS, etc.). It's designed to:
///
/// - Avoid allocations by using `Cow<'static, str>` for names
/// - Provide natural-reading error messages
/// - Be composable with custom hint types
/// - Implement `Error` trait for standard error handling
///
/// # Type Parameter
///
/// - `Hint`: The type describing what was expected. Typically one of:
///   - [`FileHint`]: Expected more bytes in a file
///   - [`TokenHint`]: Expected more tokens in a stream
///   - [`CharacterHint`]: Expected more characters in a string
///   - Custom types implementing `Display` for domain-specific hints
///
/// # Components
///
/// 1. **Name** (`Option<Cow<'static, str>>`): What ended (e.g., "file", "block comment")
/// 2. **Hint** (generic `Hint`): What was expected next
///
/// Together, these create error messages like:
/// - `"unexpected end of file, expected byte"`
/// - `"unexpected end of block comment, expected */"`
/// - `"unexpected end, expected closing brace"`
///
/// # Zero-Copy Design
///
/// `UnexpectedEnd` uses `Cow<'static, str>` for the name field, which means:
/// - Static strings (`&'static str`) involve no allocation
/// - Dynamic strings (`String`) are only allocated when necessary
/// - Most common cases (EOF, EOT, EOS) use compile-time constants
///
/// # Examples
///
/// ## Using Predefined Constants
///
/// ```rust
/// use logosky::utils::{UnexpectedEnd, UnexpectedEof, UnexpectedEot};
///
/// // Unexpected end of file
/// let eof = UnexpectedEnd::EOF;
/// assert_eq!(eof.to_string(), "unexpected end of file, expected byte");
///
/// // Unexpected end of token stream
/// let eot = UnexpectedEnd::EOT;
/// assert_eq!(eot.to_string(), "unexpected end of token stream, expected token");
/// ```
///
/// ## Custom Names and Hints
///
/// ```rust,ignore
/// use logosky::utils::UnexpectedEnd;
/// use std::borrow::Cow;
///
/// // Custom hint type for SQL parsing
/// #[derive(Debug)]
/// struct SqlHint(&'static str);
///
/// impl std::fmt::Display for SqlHint {
///     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
///         write!(f, "{}", self.0)
///     }
/// }
///
/// let error = UnexpectedEnd::with_name(
///     Cow::Borrowed("SELECT statement"),
///     SqlHint("FROM clause")
/// );
///
/// assert_eq!(
///     error.to_string(),
///     "unexpected end of SELECT statement, expected FROM clause"
/// );
/// ```
///
/// ## Transforming Hints
///
/// ```rust,ignore
/// use logosky::utils::{UnexpectedEnd, FileHint};
///
/// let file_error: UnexpectedEnd<FileHint> = UnexpectedEnd::EOF;
///
/// // Map the hint to a more specific type
/// let custom_error = file_error.map_hint(|_| "closing brace");
///
/// assert_eq!(
///     custom_error.to_string(),
///     "unexpected end of file, expected closing brace"
/// );
/// ```
///
/// ## Error Handling
///
/// ```rust,ignore
/// use logosky::utils::UnexpectedEof;
/// use std::error::Error;
///
/// fn parse_config(input: &str) -> Result<Config, Box<dyn Error>> {
///     // ... parsing logic ...
///
///     if input.is_empty() {
///         return Err(Box::new(UnexpectedEof::EOF));
///     }
///
///     Ok(config)
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnexpectedEnd<Hint> {
  name: Option<Message>,
  hint: Hint,
}

impl<Hint: Default> Default for UnexpectedEnd<Hint> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self {
      name: None,
      hint: Hint::default(),
    }
  }
}

impl<Hint> core::fmt::Display for UnexpectedEnd<Hint>
where
  Hint: core::fmt::Display,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self.name() {
      Some(name) => write!(f, "unexpected end of {name}, expected {}", self.hint),
      None => write!(f, "unexpected end, expected {}", self.hint),
    }
  }
}

impl<Hint> core::error::Error for UnexpectedEnd<Hint> where
  Hint: core::fmt::Debug + core::fmt::Display
{
}

impl UnexpectedEnd<FileHint> {
  /// A constant representing an unexpected **end of file** (EOF).
  pub const EOF: Self = Self {
    name: Some(Inner::const_new("file")),
    hint: FileHint,
  };
}

impl UnexpectedEnd<TokenHint> {
  /// A constant representing an unexpected **end of token stream** (EOT).
  pub const EOT: Self = Self {
    name: Some(Inner::const_new("token stream")),
    hint: TokenHint,
  };
}

impl UnexpectedEnd<CharacterHint> {
  /// A constant representing an unexpected **end of string** (EOS).
  pub const EOS: Self = Self {
    name: Some(Inner::const_new("string")),
    hint: CharacterHint,
  };
}

impl<Hint> UnexpectedEnd<Hint> {
  /// Creates a new unexpected end with the given hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  ///
  /// let error = UnexpectedEnd::new(FileHint);
  /// assert_eq!(error.name(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(hint: Hint) -> Self {
    Self { name: None, hint }
  }

  /// Creates a new unexpected end with the given name and hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  /// use std::borrow::Cow;
  ///
  /// let error = UnexpectedEnd::maybe_name(Some(Cow::Borrowed("string")), FileHint);
  /// assert_eq!(error.name(), Some("string"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn maybe_name(name: Option<Message>, hint: Hint) -> Self {
    Self { name, hint }
  }

  /// Creates a new unexpected end with the given name and hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  /// use std::borrow::Cow;
  ///
  /// let error = UnexpectedEnd::with_name(Cow::Borrowed("block"), FileHint);
  /// assert_eq!(error.name(), Some("block"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_name(name: Message, hint: Hint) -> Self {
    Self::maybe_name(Some(name), hint)
  }

  /// Creates a new unexpected end with the given hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, TokenHint};
  ///
  /// let error = UnexpectedEnd::with_hint(TokenHint);
  /// assert_eq!(error.name(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_hint(hint: Hint) -> Self {
    Self { name: None, hint }
  }

  /// Sets the name.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  ///
  /// let mut error = UnexpectedEnd::new(FileHint);
  /// error.set_name("expression");
  /// assert_eq!(error.name(), Some("expression"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn set_name(&mut self, name: impl Into<Message>) -> &mut Self {
    self.name = Some(name.into());
    self
  }

  /// Updates the name.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  /// use std::borrow::Cow;
  ///
  /// let mut error = UnexpectedEnd::with_name(Cow::Borrowed("old"), FileHint);
  /// error.update_name(Some("new"));
  /// assert_eq!(error.name(), Some("new"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn update_name(&mut self, name: Option<impl Into<Message>>) -> &mut Self {
    self.name = name.map(Into::into);
    self
  }

  /// Clear the name.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  /// use std::borrow::Cow;
  ///
  /// let mut error = UnexpectedEnd::with_name(Cow::Borrowed("block"), FileHint);
  /// error.clear_name();
  /// assert_eq!(error.name(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn clear_name(&mut self) -> &mut Self {
    self.name = None;
    self
  }

  /// Returns the name, if any.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::UnexpectedEnd;
  ///
  /// let error = UnexpectedEnd::EOF;
  /// assert_eq!(error.name(), Some("file"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[cfg(any(feature = "std", feature = "alloc"))]
  pub const fn name(&self) -> Option<&str> {
    match self.name.as_ref() {
      Some(name) => match name {
        Message::Borrowed(borrowed) => Some(borrowed),
        Message::Owned(owned) => Some(owned.as_str()),
      },
      None => None,
    }
  }

  /// Returns the name, if any.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::UnexpectedEnd;
  ///
  /// let error = UnexpectedEnd::EOF;
  /// assert_eq!(error.name(), Some("file"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[cfg(not(any(feature = "std", feature = "alloc")))]
  pub const fn name(&self) -> Option<&'static str> {
    self.name
  }

  /// Returns the hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  ///
  /// let error = UnexpectedEnd::EOF;
  /// // FileHint is a zero-sized type
  /// let _ = error.hint();
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn hint(&self) -> &Hint {
    &self.hint
  }

  /// Replace the hint, returning the old one.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  ///
  /// let mut error = UnexpectedEnd::EOF;
  /// let old_hint = error.replace_hint(FileHint);
  /// // old_hint is FileHint
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn replace_hint(&mut self, new: Hint) -> Hint {
    core::mem::replace(&mut self.hint, new)
  }

  /// Maps the hint to another type.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint, TokenHint};
  ///
  /// let file_error = UnexpectedEnd::EOF;
  /// let token_error = file_error.map_hint(|_| TokenHint);
  /// assert_eq!(token_error.name(), Some("file"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn map_hint<F, NewHint>(self, f: F) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd {
      name: self.name,
      hint: f(self.hint),
    }
  }

  /// Reconstructs the error with a new (optional) name and a transformed hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint, TokenHint};
  ///
  /// let file_error = UnexpectedEnd::EOF;
  /// let token_error = file_error.reconstruct(Some("block"), |_| TokenHint);
  /// assert_eq!(token_error.name(), Some("block"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn reconstruct<F, NewHint>(
    self,
    name: Option<impl Into<Message>>,
    f: F,
  ) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::maybe_name(name.map(Into::into), f(self.hint))
  }

  /// Reconstructs the error with a new name and a transformed hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint, TokenHint};
  ///
  /// let file_error = UnexpectedEnd::EOF;
  /// let token_error = file_error.reconstruct_with_name("expression", |_| TokenHint);
  /// assert_eq!(token_error.name(), Some("expression"));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn reconstruct_with_name<F, NewHint>(
    self,
    name: impl Into<Message>,
    f: F,
  ) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::with_name(name.into(), f(self.hint))
  }

  /// Reconstructs the error with a transformed hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint, TokenHint};
  /// use std::borrow::Cow;
  ///
  /// let file_error = UnexpectedEnd::with_name(Cow::Borrowed("file"), FileHint);
  /// let token_error = file_error.reconstruct_without_name(|_| TokenHint);
  /// assert_eq!(token_error.name(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn reconstruct_without_name<F, NewHint>(self, f: F) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::new(f(self.hint))
  }

  /// Consumes the unexpected end and returns the name and the hint.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use logosky::utils::{UnexpectedEnd, FileHint};
  ///
  /// let error = UnexpectedEnd::EOF;
  /// let (name, hint) = error.into_components();
  /// assert_eq!(name, Some("file".into()));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Option<Message>, Hint) {
    (self.name, self.hint)
  }
}

/// An type alias for unexpected EOF.
pub type UnexpectedEof = UnexpectedEnd<FileHint>;
/// An type alias for unexpected end of token stream.
pub type UnexpectedEot = UnexpectedEnd<TokenHint>;
/// An type alias for unexpected end of string.
pub type UnexpectedEos = UnexpectedEnd<CharacterHint>;

impl<Hint> From<Hint> for UnexpectedEnd<Hint> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from(hint: Hint) -> Self {
    Self::new(hint)
  }
}
