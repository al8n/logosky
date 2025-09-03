use derive_more::{AsMut, AsRef};

pub use logos::{Source, source::Chunk};

#[cfg(feature = "bytes")]
mod bytes;

#[cfg(feature = "bstr")]
mod bstr;

/// A wrapper around a source type to avoid the conflicting implementation of [`logos::Source`] for types implement `Deref`.
///
/// This is helpful for using [`bytes::Bytes`](https://docs.rs/bytes/latest/bytes/struct.Bytes.html) or [`bstr::BStr`](https://docs.rs/bstr/latest/bstr/struct.BStr.html).
#[derive(Clone, Copy, PartialEq, Eq, Hash, AsRef, AsMut)]
#[repr(transparent)]
pub struct CustomSource<S: ?Sized>(S);

impl<S> From<S> for CustomSource<S> {
  #[inline(always)]
  fn from(s: S) -> Self {
    Self(s)
  }
}

impl<S: ?Sized> CustomSource<S> {
  /// Creates `Source<S>` a reference of `S`
  #[inline(always)]
  pub const fn from_ref(source: &S) -> &Self {
    // Safety:
    // The cast is safe because `Source` is a transparent wrapper.
    unsafe { &*(source as *const S as *const Self) }
  }

  /// Consumes the source and returns the inner value.
  #[inline(always)]
  pub fn into_inner(self) -> S
  where
    S: Sized,
  {
    self.0
  }
}

/// A helper struct for unifying display of source.
pub struct SourceDisplay<'a, T: ?Sized>(&'a T);

impl<'a, T: ?Sized> From<&'a T> for SourceDisplay<'a, T> {
  #[inline(always)]
  fn from(t: &'a T) -> Self {
    Self(t)
  }
}

impl<T: DisplaySource + ?Sized> core::fmt::Display for SourceDisplay<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.format(f)
  }
}

/// The source text, e.g. `&[u8]`, `&str`
pub trait DisplaySource {
  /// Format the text to the given formatter
  fn format(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;
}

/// An extension trait for [`Source`]
pub trait SourceExt<'a>: DisplaySource {
  /// Returns a wrapper which implement `Display`.
  fn display(&self) -> SourceDisplay<'_, Self> {
    SourceDisplay(self)
  }
}

impl DisplaySource for str {
  #[inline]
  fn format(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    <str as core::fmt::Display>::fmt(self, fmt)
  }
}

impl DisplaySource for [u8] {
  #[inline(always)]
  #[cfg(not(feature = "bstr"))]
  fn format(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    <[u8] as core::fmt::Debug>::fmt(self, fmt)
  }

  #[inline(always)]
  #[cfg(feature = "bstr")]
  fn format(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    use ::bstr::BStr;

    <BStr as core::fmt::Display>::fmt(BStr::new(self), fmt)
  }
}
