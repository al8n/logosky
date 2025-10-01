pub use logos::{Source, source::Chunk};

#[cfg(feature = "bytes")]
mod bytes;

#[cfg(feature = "bstr")]
mod bstr;

#[cfg(feature = "hipstr")]
mod hipstr;

/// A wrapper around a source type to avoid the conflicting implementation of [`logos::Source`] for types implement `Deref`.
///
/// This is helpful for using [`bytes::Bytes`](https://docs.rs/bytes/latest/bytes/struct.Bytes.html) or [`bstr::BStr`](https://docs.rs/bstr/latest/bstr/struct.BStr.html).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct CustomSource<S: ?Sized>(S);

impl<S, T> AsRef<T> for CustomSource<S>
where
  S: AsRef<T> + ?Sized,
  T: ?Sized,
{
  #[inline(always)]
  fn as_ref(&self) -> &T {
    self.0.as_ref()
  }
}

impl<S, T> AsMut<T> for CustomSource<S>
where
  S: AsMut<T> + ?Sized,
  T: ?Sized,
{
  #[inline(always)]
  fn as_mut(&mut self) -> &mut T {
    self.0.as_mut()
  }
}

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

  /// Creates `Source<S>` a mutable reference of `S`
  #[inline(always)]
  pub const fn from_mut(source: &mut S) -> &mut Self {
    // Safety:
    // The cast is safe because `Source` is a transparent wrapper.
    unsafe { &mut *(source as *mut S as *mut Self) }
  }

  /// Returns a reference to the inner value.
  #[inline(always)]
  pub const fn as_ref(&self) -> CustomSource<&S> {
    CustomSource(&self.0)
  }

  /// Returns a mutable reference to the inner value.
  #[inline(always)]
  pub fn as_mut(&mut self) -> CustomSource<&mut S> {
    CustomSource(&mut self.0)
  }

  /// Returns the inner reference.
  #[inline(always)]
  pub const fn as_inner(&self) -> &S {
    &self.0
  }

  /// Returns a mutable reference to the inner value.
  #[inline(always)]
  pub fn as_inner_mut(&mut self) -> &mut S {
    &mut self.0
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
