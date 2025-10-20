use core::ops::Range;

use bytes::Bytes;

use super::CustomSource;

impl logos::Source for CustomSource<Bytes> {
  type Slice<'a>
    = Bytes
  where
    Self: 'a;

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  fn len(&self) -> usize {
    self.0.len()
  }

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
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

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  unsafe fn read_byte_unchecked(&self, offset: usize) -> u8 {
    // The outer unsafe fn has a Safety warnings about the offset must not exceed the bounds,
    // which is guaranteed by the outer caller.
    unsafe { *self.0.get_unchecked(offset) }
  }

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    if range.end <= self.len() {
      Some(self.0.slice(range))
    } else {
      None
    }
  }

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self::Slice<'_> {
    self.0.slice(range)
  }

  #[cfg_attr(test, inline)]
  #[cfg_attr(not(test), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    self.0.is_boundary(index)
  }
}
