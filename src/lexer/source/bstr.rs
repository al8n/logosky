use core::ops::Range;

use bstr::BStr;

use super::Source;

impl Source for BStr {
  type Slice<'a>
    = &'a [u8]
  where
    Self: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    <[u8]>::len(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn slice(&self, range: Range<usize>) -> Option<Self::Slice<'_>> {
    <[u8]>::get(self, range)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_boundary(&self, index: usize) -> bool {
    <[u8]>::is_boundary(self, index)
  }
}
