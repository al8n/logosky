use derive_more::{From, IsVariant, TryUnwrap, Unwrap};

use super::{PositionedChar, Span};

/// A compact, zero-copy description of a concrete lexeme in source.
///
/// This enum does **not** own text. It carries either:
/// - a single positioned character (`Char`), or
/// - a half-open byte span into the original source (`Range<usize>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, From)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Lexeme<Char> {
  /// A single unexpected character with its position.
  Char(PositionedChar<Char>),

  /// A half-open byte range `[start, end)` into the original source.
  ///
  /// The range must be non-empty (`start < end`) and point into the same
  /// buffer that was tokenized. Prefer UTF-8 boundary indices if you plan to
  /// slice `&str`.
  Span(Span),
}

impl<Char> Lexeme<Char> {
  /// Maps the contained character type to another type if the variant is [`Char`](Lexeme::Char).
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

  /// Return the span of bytes covered by this lexeme using a caller-provided mapping
  /// for the `Char` variant.
  #[inline]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Span {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        Span::from(pos..(pos + len_of(pc.char())))
      }
      Self::Span(r) => *r,
    }
  }

  /// Return the span of bytes covered by this lexeme.
  #[inline]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        Span::from(pos..(pos + pc.char().len()))
      }
      Self::Span(r) => *r,
    }
  }

  /// Bump the span by `n` or the position of the char by `n`.
  #[inline]
  pub const fn bump(&mut self, n: usize) -> &mut Self {
    match self {
      Self::Char(positioned_char) => {
        positioned_char.bump_position(n);
      }
      Self::Span(span) => {
        span.bump_span(n);
      },
    }

    self
  }
}

/// A zero-copy *unexpected lexeme* paired with a diagnostic hint.
///
/// Instead of owning text, this stores:
/// - the *lexeme* of unexpected fragment (`Char` or `Span`), and
/// - a *hint* describing what was expected next (any type you choose).
///
/// The hint typically implements `Display` in your error type, but it’s left
/// unconstrained here so you can carry richer structured info.
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
  /// Creates a new `UnexpectedLexeme` from the given data and hint.
  #[inline(always)]
  pub const fn new(lexeme: Lexeme<Char>, hint: Hint) -> Self {
    Self { lexeme, hint }
  }

  /// Construct from a positioned character.
  #[inline]
  pub const fn from_char(pc: PositionedChar<Char>, hint: Hint) -> Self {
    Self::new(Lexeme::Char(pc), hint)
  }

  /// Construct from a byte span.
  #[inline]
  pub const fn from_span_const(span: Span, hint: Hint) -> Self {
    Self::new(Lexeme::Span(span), hint)
  }

  /// Construct from a byte span.
  #[inline]
  pub fn from_span(span: impl Into<Span>, hint: Hint) -> Self {
    Self::new(Lexeme::Span(span.into()), hint)
  }

  /// Returns a reference to the unexpected lexeme.
  #[inline(always)]
  pub const fn lexeme(&self) -> &Lexeme<Char> {
    &self.lexeme
  }

  /// Returns a reference to the hint.
  #[inline(always)]
  pub const fn hint(&self) -> &Hint {
    &self.hint
  }

  /// Returns a mutable reference to the unexpected lexeme.
  #[inline(always)]
  pub const fn lexeme_mut(&mut self) -> &mut Lexeme<Char> {
    &mut self.lexeme
  }

  /// Returns a mutable reference to the hint.
  #[inline(always)]
  pub const fn hint_mut(&mut self) -> &mut Hint {
    &mut self.hint
  }

  /// Consume into `(lexeme, hint)`.
  #[inline]
  pub fn into_components(self) -> (Lexeme<Char>, Hint) {
    (self.lexeme, self.hint)
  }

  /// Consume and return only the lexeme.
  #[inline]
  pub fn into_lexeme(self) -> Lexeme<Char> {
    self.lexeme
  }

  /// Consume and return only the hint.
  #[inline]
  pub fn into_hint(self) -> Hint {
    self.hint
  }

  /// Returns the span of bytes covered by this lexeme using a caller-provided mapping
  /// for the `Char` variant.
  #[inline]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Span {
    self.lexeme.span_with(len_of)
  }

  /// Returns the span of bytes covered by this lexeme.
  #[inline]
  pub fn span(&self) -> Span
  where
    Char: CharLen,
  {
    self.lexeme.span()
  }

  /// Maps the contained character type to another type.
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

  /// Maps the contained hint type to another type.
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

  /// Maps both the contained character and hint types to other types.
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
}

/// A trait for character-like types that can report their encoded length in bytes.
///
/// Implemented for `u8` (1 byte), `char` (`len_utf8()`), and references thereof.
/// If your `Char` is something else, prefer `span_with` and pass a length function.
#[allow(clippy::len_without_is_empty)]
pub trait CharLen: sealed::Sealed {
  /// Returns the length of this character in bytes.
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
