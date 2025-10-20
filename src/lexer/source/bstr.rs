use core::ops::Range;

use bstr::BStr;

use super::CustomSource;

impl<'a> From<&'a BStr> for &'a CustomSource<BStr> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from(s: &'a BStr) -> Self {
    CustomSource::from_ref(s)
  }
}

impl logos::Source for CustomSource<BStr> {
  type Slice<'a>
    = &'a [u8]
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    self.0.len()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
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

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn read_byte_unchecked(&self, offset: usize) -> u8 {
    // The outer unsafe fn has a Safety warnings about the offset must not exceed the bounds,
    // which is guaranteed by the outer caller.
    unsafe { *self.0.get_unchecked(offset) }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    self.0.slice(range)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self::Slice<'_> {
    // Safety: will deref to [u8] implementation
    unsafe { self.0.slice_unchecked(range) }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    self.0.is_boundary(index)
  }
}
