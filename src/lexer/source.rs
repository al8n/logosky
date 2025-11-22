use core::ops::Range;

#[cfg(feature = "bytes")]
mod bytes;

#[cfg(feature = "bstr")]
mod bstr;

#[cfg(feature = "hipstr")]
mod hipstr;

/// The slice type returned by lexers' sources.
pub trait Slice<'source>: PartialEq + Eq + core::fmt::Debug {
  /// The character type used by the lexer.
  ///
  /// - Use `char` for text-based lexers processing UTF-8 strings
  /// - Use `u8` for byte-based lexers processing binary data or non-UTF-8 input
  ///
  /// This type must match the character type used by the Logos lexer's source.
  type Char: Copy + core::fmt::Debug + PartialEq + Eq + core::hash::Hash;

  /// An iterator over the characters in the slice.
  type Iter<'a>: Iterator<Item = Self::Char>
  where
    Self: 'a;

  /// An iterator over the characters in the slice with their offsets to the start of the slice.
  type PositionedIter<'a>: Iterator<Item = (usize, Self::Char)>
  where
    Self: 'a;

  /// Returns an iterator over the characters in the slice.
  fn iter<'a>(&'a self) -> Self::Iter<'a>
  where
    Self: 'a;

  /// Returns an iterator over the characters in the slice with their offsets to the start of the slice.
  fn positioned_iter<'a>(&'a self) -> Self::PositionedIter<'a>
  where
    Self: 'a;

  /// Returns the length of the slice.
  fn len(&self) -> usize;

  /// Returns `true` if the slice is empty.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }
}

impl<'source> Slice<'source> for &'source [u8] {
  type Char = u8;

  type Iter<'a>
    = core::iter::Copied<core::slice::Iter<'a, u8>>
  where
    Self: 'a;

  type PositionedIter<'a>
    = core::iter::Enumerate<core::iter::Copied<core::slice::Iter<'a, u8>>>
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn iter<'a>(&'a self) -> Self::Iter<'a>
  where
    Self: 'a,
  {
    <[u8]>::iter(self).copied()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn positioned_iter<'a>(&'a self) -> Self::PositionedIter<'a>
  where
    Self: 'a,
  {
    <[u8]>::iter(self).copied().enumerate()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <[u8]>::len(self)
  }
}

impl<'source> Slice<'source> for &'source str {
  type Char = char;

  type Iter<'a>
    = core::str::Chars<'a>
  where
    Self: 'a;

  type PositionedIter<'a>
    = core::str::CharIndices<'a>
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn iter<'a>(&'a self) -> Self::Iter<'a>
  where
    Self: 'a,
  {
    self.chars()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn positioned_iter<'a>(&'a self) -> Self::PositionedIter<'a>
  where
    Self: 'a,
  {
    self.char_indices()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <str>::len(self)
  }
}

/// The source trait for lexers
pub trait Source {
  /// A type this `Source` can be sliced into.
  type Slice<'source>: Slice<'source>
  where
    Self: 'source;

  /// Returns `true` if the source is empty.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Length of the source
  fn len(&self) -> usize;

  /// Get a slice of the source at given range. This is analogous to
  /// `slice::get(range)`.
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>>;

  /// For `&str` sources attempts to find the closest `char` boundary at which source
  /// can be sliced, starting from `index`.
  ///
  /// For binary sources (`&[u8]`) this should just return `index` back.
  #[inline]
  fn find_boundary(&self, index: usize) -> usize {
    index
  }

  /// Check if `index` is valid for this `Source`, that is:
  ///
  /// + It's not larger than the byte length of the `Source`.
  /// + (`str` only) It doesn't land in the middle of a UTF-8 code point.
  fn is_boundary(&self, index: usize) -> bool;
}

impl Source for [u8] {
  type Slice<'source>
    = &'source [u8]
  where
    Self: 'source;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    self.len()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    self.get(range)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    index <= self.len()
  }
}

impl Source for str {
  type Slice<'source>
    = &'source str
  where
    Self: 'source;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <str>::len(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    self.get(range)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    self.is_char_boundary(index)
  }
}
