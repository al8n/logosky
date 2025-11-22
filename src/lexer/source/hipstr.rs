use core::ops::Range;

use hipstr::{HipByt, HipStr};

use super::{Slice, Source};

impl<'source> Slice<'source> for HipStr<'source> {
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
    <HipStr<'source>>::len(self)
  }
}

impl<'h> Source for HipStr<'h> {
  type Slice<'a>
    = HipStr<'a>
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <HipStr<'h>>::len(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    if range.end <= self.len() {
      Some(self.slice(range))
    } else {
      None
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    self.is_char_boundary(index)
  }
}

impl<'source> Slice<'source> for HipByt<'source> {
  type Char = u8;

  type Iter<'a>
    = core::iter::Copied<core::slice::Iter<'a, u8>>
  where
    Self: 'a;

  type PositionedIter<'a>
    = core::iter::Enumerate<Self::Iter<'a>>
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
    self.iter().enumerate()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <HipByt<'source>>::len(self)
  }
}

impl Source for HipByt<'_> {
  type Slice<'a>
    = HipByt<'a>
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <HipByt<'_>>::len(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    if range.end <= self.len() {
      Some(self.slice(range))
    } else {
      None
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    <[u8]>::is_boundary(self, index)
  }
}
