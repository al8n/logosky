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

