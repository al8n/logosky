/// A trait for checking if two values are equivalent.
pub trait Equivalent<T: ?Sized> {
  /// Returns `true` if `self` is equivalent to `other`.
  fn equivalent(&self, other: &T) -> bool;
}

impl<T, O> Equivalent<O> for &T
where
  T: Equivalent<O> + ?Sized,
  O: ?Sized,
{
  #[inline(always)]
  fn equivalent(&self, other: &O) -> bool {
    T::equivalent(*self, other)
  }
}

impl<T, O> Equivalent<O> for &mut T
where
  T: Equivalent<O> + ?Sized,
  O: ?Sized,
{
  #[inline(always)]
  fn equivalent(&self, other: &O) -> bool {
    T::equivalent(*self, other)
  }
}

impl<T> Equivalent<T> for str
where
  T: AsRef<[u8]> + ?Sized,
{
  #[inline(always)]
  fn equivalent(&self, other: &T) -> bool {
    self.as_bytes().eq(other.as_ref())
  }
}

impl<T> Equivalent<T> for [u8]
where
  T: AsRef<[u8]> + ?Sized,
{
  #[inline(always)]
  fn equivalent(&self, other: &T) -> bool {
    self.eq(other.as_ref())
  }
}

const fn __assert_equivalent_impl<T, O>()
where
  O: Equivalent<T> + ?Sized,
  T: ?Sized,
{
}

const _: () = {
  __assert_equivalent_impl::<str, [u8]>();
  __assert_equivalent_impl::<[u8], str>();
  __assert_equivalent_impl::<str, str>();
  __assert_equivalent_impl::<[u8], [u8]>();
  __assert_equivalent_impl::<&str, &[u8]>();
  __assert_equivalent_impl::<&[u8], &str>();
  __assert_equivalent_impl::<&str, &str>();
  __assert_equivalent_impl::<&[u8], &[u8]>();
};

#[cfg(feature = "bytes")]
const _: () = {
  use bytes::Bytes;

  impl Equivalent<str> for Bytes {
    #[inline(always)]
    fn equivalent(&self, other: &str) -> bool {
      self.as_ref().eq(other.as_bytes())
    }
  }

  impl Equivalent<[u8]> for Bytes {
    #[inline(always)]
    fn equivalent(&self, other: &[u8]) -> bool {
      self.as_ref().eq(other)
    }
  }

  impl Equivalent<Bytes> for Bytes {
    #[inline(always)]
    fn equivalent(&self, other: &Bytes) -> bool {
      self.eq(other)
    }
  }

  __assert_equivalent_impl::<Bytes, str>();
  __assert_equivalent_impl::<Bytes, [u8]>();
  __assert_equivalent_impl::<str, Bytes>();
  __assert_equivalent_impl::<[u8], Bytes>();
};

#[cfg(feature = "hipstr")]
const _: () = {
  use hipstr::{HipByt, HipStr};

  const _: () = __assert_equivalent_impl::<HipStr<'_>, str>();
  const _: () = __assert_equivalent_impl::<HipByt<'_>, str>();
};
