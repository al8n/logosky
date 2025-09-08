use core::fmt::Display;

use crate::source::CustomSource;

use super::PositionedChar;

/// A trait for displaying in a human-friendly way.
pub trait DisplayHuman {
  /// Formats the value in a human-friendly way.
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;

  /// Returns a wrapper which implement `Display`.
  #[inline(always)]
  fn display(&self) -> HumanDisplay<'_, Self> {
    HumanDisplay(self)
  }
}

impl<T: DisplayHuman + ?Sized> DisplayHuman for &T {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).format(f)
  }
}

impl<T: DisplayHuman + ?Sized> DisplayHuman for CustomSource<T> {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_ref().format(f)
  }
}

impl DisplayHuman for u8 {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    if self.is_ascii() {
      write!(f, "{}", *self as char)
    } else {
      self.fmt(f)
    }
  }
}

impl DisplayHuman for char {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt(f)
  }
}

impl<T: DisplayHuman> DisplayHuman for PositionedChar<T> {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.char_ref().format(f)
  }
}

impl DisplayHuman for str {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt(f)
  }
}

impl DisplayHuman for [u8] {
  #[cfg(not(feature = "bstr"))]
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match core::str::from_utf8(self) {
      Ok(s) => s.fmt(f),
      Err(_) => core::fmt::Debug::fmt(self, f),
    }
  }

  #[cfg(feature = "bstr")]
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    bstr::BStr::new(self).fmt(f)
  }
}

impl DisplayHuman for [char] {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    for c in self {
      c.format(f)?;
    }
    Ok(())
  }
}

impl<const N: usize> DisplayHuman for [u8; N] {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_slice().format(f)
  }
}

impl<const N: usize> DisplayHuman for [char; N] {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_slice().format(f)
  }
}

#[cfg(feature = "bytes")]
impl DisplayHuman for bytes::Bytes {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_ref().format(f)
  }
}

#[cfg(feature = "bstr")]
impl DisplayHuman for bstr::BStr {
  #[inline]
  fn format(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt(f)
  }
}

/// A helper struct for displaying in a human-friendly way.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanDisplay<'a, T: ?Sized>(pub(crate) &'a T);

impl<'a, T: ?Sized> From<&'a T> for HumanDisplay<'a, T> {
  #[inline(always)]
  fn from(t: &'a T) -> Self {
    Self(t)
  }
}

impl<T: DisplayHuman + ?Sized> core::fmt::Display for HumanDisplay<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.format(f)
  }
}
