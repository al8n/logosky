use core::ops::Range;

use derive_more::{From, IsVariant, TryUnwrap, Unwrap};

use super::PositionedChar;

/// A compact, zero-copy description of the concrete lexeme that was unexpected.
///
/// This enum does **not** own source text. It carries either:
/// - a single positioned character (`Char`), or
/// - a half-open byte span into the original source (`Range<usize>`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, From)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum UnexpectedLexemeKind<Char> {
  /// A single unexpected character with its position.
  Char(PositionedChar<Char>),

  /// A half-open byte range `[start, end)` into the original source.
  ///
  /// The range must be non-empty (`start < end`) and point into the same
  /// buffer that was tokenized. Prefer UTF-8 boundary indices if you plan to
  /// slice `&str`.
  Span(Range<usize>),
}

impl<Char> UnexpectedLexemeKind<Char> {
  /// Maps the contained character type to another type if the variant is [`Char`](UnexpectedLexemeKind::Char).
  #[inline]
  pub fn map<F, NewChar>(self, f: F) -> UnexpectedLexemeKind<NewChar>
  where
    F: FnOnce(Char) -> NewChar,
  {
    match self {
      Self::Char(pc) => UnexpectedLexemeKind::Char(pc.map(f)),
      Self::Span(r) => UnexpectedLexemeKind::Span(r),
    }
  }

  /// Return the span of bytes covered by this lexeme using a caller-provided mapping
  /// for the `Char` variant.
  #[inline]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Range<usize> {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        pos..(pos + len_of(pc.char()))
      },
      Self::Span(r) => r.clone(),
    }
  }

  /// Return the span of bytes covered by this lexeme.
  #[inline]
  pub fn span(&self) -> Range<usize> where Char: CharLen {
    match self {
      Self::Char(pc) => {
        let pos = pc.position();
        pos..(pos + pc.char().len())
      },
      Self::Span(r) => r.clone(),
    }
  }
}

/// A zero-copy *unexpected lexeme* paired with a diagnostic hint.
///
/// Instead of owning text, this stores:
/// - the *kind* of unexpected fragment (`Char` or `Span`), and
/// - a *hint* describing what was expected next (any type you choose).
///
/// The hint typically implements `Display` in your error type, but it’s left
/// unconstrained here so you can carry richer structured info.
pub struct UnexpectedLexeme<Char, Hint> {
  kind: UnexpectedLexemeKind<Char>,
  hint: Hint,
}

impl<Char, Hint> UnexpectedLexeme<Char, Hint> {
  /// Creates a new `UnexpectedLexeme` from the given data and hint.
  #[inline(always)]
  pub const fn new(kind: UnexpectedLexemeKind<Char>, hint: Hint) -> Self {
    Self { kind, hint }
  }

  /// Construct from a positioned character.
  #[inline]
  pub const fn from_char(pc: PositionedChar<Char>, hint: Hint) -> Self {
    Self::new(UnexpectedLexemeKind::Char(pc), hint)
  }

  /// Construct from a byte span.
  #[inline]
  pub const fn from_span(span: Range<usize>, hint: Hint) -> Self {
    Self::new(UnexpectedLexemeKind::Span(span), hint)
  }

  /// Returns a reference to the unexpected lexeme kind.
  #[inline(always)]
  pub const fn kind(&self) -> &UnexpectedLexemeKind<Char> {
    &self.kind
  }

  /// Returns a reference to the hint.
  #[inline(always)]
  pub const fn hint(&self) -> &Hint {
    &self.hint
  }

  /// Returns a mutable reference to the unexpected lexeme kind.
  #[inline(always)]
  pub const fn kind_mut(&mut self) -> &mut UnexpectedLexemeKind<Char> {
    &mut self.kind
  }

  /// Returns a mutable reference to the hint.
  #[inline(always)]
  pub const fn hint_mut(&mut self) -> &mut Hint {
    &mut self.hint
  }

  /// Consume into `(kind, hint)`.
  #[inline]
  pub fn into_components(self) -> (UnexpectedLexemeKind<Char>, Hint) {
    (self.kind, self.hint)
  }

  /// Consume and return only the kind.
  #[inline]
  pub fn into_kind(self) -> UnexpectedLexemeKind<Char> {
    self.kind
  }

  /// Consume and return only the hint.
  #[inline]
  pub fn into_hint(self) -> Hint {
    self.hint
  }

  /// Returns the span of bytes covered by this lexeme using a caller-provided mapping
  /// for the `Char` variant.
  #[inline]
  pub fn span_with(&self, len_of: impl FnOnce(&Char) -> usize) -> Range<usize> {
    self.kind.span_with(len_of)
  }

  /// Returns the span of bytes covered by this lexeme.
  #[inline]
  pub fn span(&self) -> Range<usize> where Char: CharLen {
    self.kind.span()
  }

  /// Maps the contained character type to another type.
  #[inline]
  pub fn map_char<F, NewChar>(self, f: F) -> UnexpectedLexeme<NewChar, Hint>
  where
    F: FnMut(Char) -> NewChar,
  {
    UnexpectedLexeme {
      kind: self.kind.map(f),
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
      kind: self.kind,
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
      kind: self.kind.map(f),
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

