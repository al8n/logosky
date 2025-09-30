use core::fmt;

use crate::source::CustomSource;

use super::PositionedChar;

/// A trait for displaying in a human-friendly way.
pub trait DisplayHuman {
  /// Formats the value in a human-friendly way.
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;

  /// Returns a wrapper which implement `Display`.
  #[inline(always)]
  fn display(&self) -> HumanDisplay<'_, Self> {
    HumanDisplay(self)
  }
}

impl<T: DisplayHuman + ?Sized> DisplayHuman for &T {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt(f)
  }
}

impl<T: DisplayHuman + ?Sized> DisplayHuman for CustomSource<T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_inner().fmt(f)
  }
}

impl DisplayHuman for u8 {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    if self.is_ascii() {
      write!(f, "{}", *self as char)
    } else {
      fmt::Display::fmt(self, f)
    }
  }
}

macro_rules! impl_display_human_for_primitive {
  ($($ty:ty),+) => {
    $(
      impl DisplayHuman for $ty {
        #[inline]
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
          fmt::Display::fmt(self, f)
        }
      }
    )*
  };
}

impl_display_human_for_primitive!(
  u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64, char, str
);

impl<T: DisplayHuman> DisplayHuman for PositionedChar<T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.char_ref().fmt(f)
  }
}

impl DisplayHuman for [u8] {
  #[cfg(not(feature = "bstr"))]
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match core::str::from_utf8(self) {
      Ok(s) => s.fmt(f),
      Err(_) => core::fmt::Debug::fmt(self, f),
    }
  }

  #[cfg(feature = "bstr")]
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    bstr::BStr::new(self).fmt(f)
  }
}

impl DisplayHuman for [char] {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    for c in self {
      c.fmt(f)?;
    }
    Ok(())
  }
}

impl<const N: usize> DisplayHuman for [u8; N] {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_slice().fmt(f)
  }
}

impl<const N: usize> DisplayHuman for [char; N] {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_slice().fmt(f)
  }
}

#[cfg(feature = "bytes")]
impl DisplayHuman for bytes::Bytes {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.as_ref().fmt(f)
  }
}

#[cfg(feature = "bstr")]
impl DisplayHuman for bstr::BStr {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    fmt::Display::fmt(self, f)
  }
}

/// A helper struct for displaying in a human-friendly way.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HumanDisplay<'a, T: ?Sized>(&'a T);

impl<T: DisplayHuman + ?Sized> core::fmt::Display for HumanDisplay<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.fmt(f)
  }
}
