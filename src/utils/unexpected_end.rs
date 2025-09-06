use std::borrow::Cow;

use derive_more::Display;

/// A zero-sized marker that describes what was expected when the *file/input bytes* ended.
///
/// Displayed as `"byte"` so messages read naturally:
/// `"unexpected end of file, expected byte"`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("byte")]
pub struct FileHint;

/// A zero-sized marker that describes what was expected when the *token stream* ended.
///
/// Displayed as `"token"` so messages read naturally:
/// `"unexpected end of token stream, expected token"`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("token")]
pub struct TokenHint;

/// A zero-sized marker that describes what was expected when the *string* ended.
///
/// Displayed as `"token"` so messages read naturally:
/// `"unexpected end of token stream, expected token"`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Display)]
#[display("character")]
pub struct CharacterHint;

/// A zero-copy description of an *unexpected end* (EOF/EOT) for diagnostics.
///
/// This type intentionally avoids owning strings. It stores:
/// - an optional **name** for the thing that ended (e.g., `"file"`, `"token stream"`,
///   `"string"`, `"block comment"`), and
/// - a **hint** describing what was expected next (e.g., `TokenHint`, `FileHint`,
///   or any custom type that implements `Display`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnexpectedEnd<Hint> {
  name: Option<Cow<'static, str>>,
  hint: Hint,
}

impl<Hint: Default> Default for UnexpectedEnd<Hint> {
  #[inline]
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
  #[inline]
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
    name: Some(Cow::Borrowed("file")),
    hint: FileHint,
  };
}

impl UnexpectedEnd<TokenHint> {
  /// A constant representing an unexpected **end of token stream** (EOT).
  pub const EOT: Self = Self {
    name: Some(Cow::Borrowed("token stream")),
    hint: TokenHint,
  };
}

impl UnexpectedEnd<CharacterHint> {
  /// A constant representing an unexpected **end of string** (EOS).
  pub const EOS: Self = Self {
    name: Some(Cow::Borrowed("string")),
    hint: CharacterHint,
  };
}

impl<Hint> UnexpectedEnd<Hint> {
  /// Creates a new unexpected end with the given hint.
  #[inline]
  pub const fn new(hint: Hint) -> Self {
    Self { name: None, hint }
  }

  /// Creates a new unexpected end with the given name and hint.
  #[inline]
  pub const fn maybe_name(name: Option<Cow<'static, str>>, hint: Hint) -> Self {
    Self { name, hint }
  }

  /// Creates a new unexpected end with the given name and hint.
  #[inline]
  pub const fn with_name(name: Cow<'static, str>, hint: Hint) -> Self {
    Self::maybe_name(Some(name), hint)
  }

  /// Creates a new unexpected end with the given hint.
  #[inline]
  pub const fn with_hint(hint: Hint) -> Self {
    Self { name: None, hint }
  }

  /// Sets the name.
  #[inline]
  pub fn set_name(&mut self, name: impl Into<Cow<'static, str>>) -> &mut Self {
    self.name = Some(name.into());
    self
  }

  /// Updates the name.
  #[inline]
  pub fn update_name(&mut self, name: Option<impl Into<Cow<'static, str>>>) -> &mut Self {
    self.name = name.map(Into::into);
    self
  }

  /// Clear the name.
  #[inline]
  pub fn clear_name(&mut self) -> &mut Self {
    self.name = None;
    self
  }

  /// Returns the name, if any.
  #[inline]
  pub const fn name(&self) -> Option<&str> {
    match self.name.as_ref() {
      Some(name) => match name {
        Cow::Borrowed(borrowed) => Some(borrowed),
        Cow::Owned(owned) => Some(owned.as_str()),
      },
      None => None,
    }
  }

  /// Returns the hint.
  #[inline]
  pub const fn hint(&self) -> &Hint {
    &self.hint
  }

  /// Replace the hint, returning the old one.
  #[inline]
  pub fn replace_hint(&mut self, new: Hint) -> Hint {
    core::mem::replace(&mut self.hint, new)
  }

  /// Maps the hint to another type.
  #[inline]
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
  #[inline]
  pub fn reconstruct<F, NewHint>(
    self,
    name: Option<impl Into<Cow<'static, str>>>,
    f: F,
  ) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::maybe_name(name.map(Into::into), f(self.hint))
  }

  /// Reconstructs the error with a new name and a transformed hint.
  #[inline]
  pub fn reconstruct_with_name<F, NewHint>(
    self,
    name: impl Into<Cow<'static, str>>,
    f: F,
  ) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::with_name(name.into(), f(self.hint))
  }

  /// Reconstructs the error with a transformed hint.
  #[inline]
  pub fn reconstruct_without_name<F, NewHint>(self, f: F) -> UnexpectedEnd<NewHint>
  where
    F: FnOnce(Hint) -> NewHint,
  {
    UnexpectedEnd::new(f(self.hint))
  }

  /// Consumes the unexpected end and returns the name and the hint.
  #[inline]
  pub fn into_components(self) -> (Option<Cow<'static, str>>, Hint) {
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
  #[inline]
  fn from(hint: Hint) -> Self {
    Self::new(hint)
  }
}
