#![allow(single_use_lifetimes)]

mod sealed {
  pub trait Sealed<T: ?Sized> {}

  impl<T, O> Sealed<O> for &T where T: Sealed<O> + ?Sized {}
}

/// A trait for converting to an equivalent type.
///
/// e.g. `&[u8]` is equivalent to [`bytes::Bytes`](https://docs.rs/bytes/latest/bytes/struct.Bytes.html)
pub trait ToEquivalent<T>: sealed::Sealed<T> {
  /// Converts this element to an equivalent type `T`.
  fn to_equivalent(&self) -> T;
}

impl<T, O> ToEquivalent<O> for &T
where
  T: ToEquivalent<O> + ?Sized,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn to_equivalent(&self) -> O {
    T::to_equivalent(self)
  }
}

impl sealed::Sealed<str> for str {}
impl<'de: 'a, 'a> sealed::Sealed<&'a str> for &'de str {}

impl sealed::Sealed<[u8]> for [u8] {}
impl<'de: 'a, 'a> sealed::Sealed<&'a [u8]> for &'de [u8] {}

impl<'de: 'a, 'a> ToEquivalent<&'a str> for &'de str {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn to_equivalent(&self) -> &'a str {
    self
  }
}

impl<'de: 'a, 'a> ToEquivalent<&'a [u8]> for &'de [u8] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn to_equivalent(&self) -> &'a [u8] {
    self
  }
}

/// A trait for converting into an equivalent type.
///
/// e.g. `&[u8]` is equivalent to [`bytes::Bytes`](https://docs.rs/bytes/latest/bytes/struct.Bytes.html)
pub trait IntoEquivalent<T>: sealed::Sealed<T> {
  /// Consumes this element and converts it into an equivalent type `T`.
  fn into_equivalent(self) -> T;
}

impl<'de: 'a, 'a> IntoEquivalent<&'a str> for &'de str {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_equivalent(self) -> &'a str {
    self
  }
}

impl<'de: 'a, 'a> IntoEquivalent<&'a [u8]> for &'de [u8] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_equivalent(self) -> &'a [u8] {
    self
  }
}

#[cfg(feature = "bytes")]
const _: () = {
  use crate::source::CustomSource;
  use bytes::Bytes;
  use sealed::Sealed;

  impl Sealed<Bytes> for [u8] {}

  impl ToEquivalent<Bytes> for [u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> Bytes {
      Bytes::copy_from_slice(self)
    }
  }

  impl IntoEquivalent<Bytes> for &[u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> Bytes {
      Bytes::copy_from_slice(self)
    }
  }

  impl Sealed<CustomSource<Bytes>> for [u8] {}

  impl ToEquivalent<CustomSource<Bytes>> for [u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> CustomSource<Bytes> {
      CustomSource::from(Bytes::copy_from_slice(self))
    }
  }

  impl IntoEquivalent<CustomSource<Bytes>> for &[u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> CustomSource<Bytes> {
      CustomSource::from(Bytes::copy_from_slice(self))
    }
  }

  fn __assert_bytes_to_equivalent_impl() {
    fn _assert<T: ToEquivalent<Bytes> + ?Sized>() {}

    _assert::<[u8]>();
    _assert::<&[u8]>();
  }

  fn __assert_bytes_into_equivalent_impl() {
    fn _assert<T: IntoEquivalent<Bytes> + ?Sized>() {}

    _assert::<&[u8]>();
  }
};

#[cfg(feature = "hipstr")]
const _: () = {
  use crate::source::CustomSource;
  use hipstr::{HipByt, HipStr};
  use sealed::Sealed;

  impl Sealed<HipStr<'_>> for str {}

  impl<'a> ToEquivalent<HipStr<'a>> for str {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> HipStr<'a> {
      HipStr::from(self)
    }
  }

  impl<'a> IntoEquivalent<HipStr<'a>> for &str {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> HipStr<'a> {
      HipStr::from(self)
    }
  }

  impl Sealed<CustomSource<HipStr<'_>>> for str {}

  impl<'a> ToEquivalent<CustomSource<HipStr<'a>>> for str {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> CustomSource<HipStr<'a>> {
      CustomSource::from(HipStr::from(self))
    }
  }

  impl<'b> IntoEquivalent<CustomSource<HipStr<'b>>> for &str {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> CustomSource<HipStr<'b>> {
      CustomSource::from(HipStr::from(self))
    }
  }

  impl Sealed<HipByt<'_>> for [u8] {}

  impl<'a> ToEquivalent<HipByt<'a>> for [u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> HipByt<'a> {
      HipByt::from(self)
    }
  }

  impl<'a> IntoEquivalent<HipByt<'a>> for &[u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> HipByt<'a> {
      HipByt::from(self)
    }
  }

  impl Sealed<CustomSource<HipByt<'_>>> for [u8] {}

  impl<'a> ToEquivalent<CustomSource<HipByt<'a>>> for [u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn to_equivalent(&self) -> CustomSource<HipByt<'a>> {
      CustomSource::from(HipByt::from(self))
    }
  }

  impl<'b> IntoEquivalent<CustomSource<HipByt<'b>>> for &[u8] {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_equivalent(self) -> CustomSource<HipByt<'b>> {
      CustomSource::from(HipByt::from(self))
    }
  }
};
