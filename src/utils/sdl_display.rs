
/// A trait for displaying in a SDL.
pub trait DisplaySDL {
  /// Formats the value in a SDL.
  fn fmt_sdl(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;

  /// Formats the value in a compact SDL.
  #[inline(always)]
  fn fmt_sdl_compact(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt_sdl(f)
  }

  /// Returns a wrapper which implement `Display`.
  #[inline(always)]
  fn display(&self) -> SDLDisplay<'_, Self> {
    SDLDisplay(self)
  }
}

impl<T: DisplaySDL + ?Sized> DisplaySDL for &T {
  #[inline]
  fn fmt_sdl(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt_sdl(f)
  }

  #[inline(always)]
  fn fmt_sdl_compact(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt_sdl_compact(f)
  }
}

/// A helper struct for displaying in a SDL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SDLDisplay<'a, T: ?Sized>(&'a T);

impl<T: DisplaySDL + ?Sized> core::fmt::Display for SDLDisplay<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.0.fmt_sdl(f)
  }
}
