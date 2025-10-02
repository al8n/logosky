use core::ops::Range;

use hipstr::{HipByt, HipStr};

use super::CustomSource;

impl<'h> logos::Source for CustomSource<HipStr<'h>> {
  type Slice<'a>
    = HipStr<'h>
  where
    Self: 'a;

  #[inline(always)]
  fn len(&self) -> usize {
    self.0.len()
  }

  #[inline(always)]
  fn read<'a, Chunk>(&'a self, offset: usize) -> Option<Chunk>
  where
    Chunk: logos::source::Chunk<'a>,
  {
    if offset + (Chunk::SIZE - 1) < self.len() {
      Some(unsafe { Chunk::from_ptr(self.0.as_ptr().add(offset)) })
    } else {
      None
    }
  }

  #[inline(always)]
  unsafe fn read_byte_unchecked(&self, offset: usize) -> u8 {
    // The outer unsafe fn has a Safety warnings about the offset must not exceed the bounds,
    // which is guaranteed by the outer caller.
    unsafe { *self.0.as_bytes().get_unchecked(offset) }
  }

  #[inline(always)]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    if range.end <= self.len() {
      Some(self.0.slice(range))
    } else {
      None
    }
  }

  #[inline(always)]
  unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self::Slice<'_> {
    // Safety: the inner unsafe has the same safety requirement as the outer one
    unsafe { self.0.slice_unchecked(range) }
  }

  #[inline(always)]
  fn is_boundary(&self, index: usize) -> bool {
    self.0.is_boundary(index)
  }
}

impl<'h> logos::Source for CustomSource<HipByt<'h>> {
  type Slice<'a>
    = HipByt<'h>
  where
    Self: 'a;

  #[inline(always)]
  fn len(&self) -> usize {
    self.0.len()
  }

  #[inline(always)]
  fn read<'a, Chunk>(&'a self, offset: usize) -> Option<Chunk>
  where
    Chunk: logos::source::Chunk<'a>,
  {
    if offset + (Chunk::SIZE - 1) < self.len() {
      Some(unsafe { Chunk::from_ptr(self.0.as_ptr().add(offset)) })
    } else {
      None
    }
  }

  #[inline(always)]
  unsafe fn read_byte_unchecked(&self, offset: usize) -> u8 {
    // The outer unsafe fn has a Safety warnings about the offset must not exceed the bounds,
    // which is guaranteed by the outer caller.
    unsafe { *self.0.get_unchecked(offset) }
  }

  #[inline(always)]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    if range.end <= self.len() {
      Some(self.0.slice(range))
    } else {
      None
    }
  }

  #[inline(always)]
  unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self::Slice<'_> {
    // Safety: the inner unsafe has the same safety requirement as the outer one
    unsafe { self.0.slice_unchecked(range) }
  }

  #[inline(always)]
  fn is_boundary(&self, index: usize) -> bool {
    self.0.is_boundary(index)
  }
}
