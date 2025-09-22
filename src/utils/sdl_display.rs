/// A trait for displaying in a SDL.
pub trait DisplaySDL {
  /// Formats the value in a SDL.
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result;

  /// Formats the value in a compact SDL.
  #[inline(always)]
  fn fmt_compact(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt(f)
  }

  /// Formats the value in a pretty SDL.
  #[inline(always)]
  fn fmt_pretty(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.fmt(f)
  }

  /// Returns a wrapper which implement `Display`.
  #[inline(always)]
  fn display(&self) -> SDLDisplay<'_, Self> {
    SDLDisplay::default(self)
  }

  /// Returns a wrapper which implement `Display` in a compact SDL.
  #[inline(always)]
  fn display_compact(&self) -> SDLDisplay<'_, Self> {
    SDLDisplay::compact(self)
  }

  /// Returns a wrapper which implement `Display` in a pretty SDL.
  #[inline(always)]
  fn display_pretty(&self) -> SDLDisplay<'_, Self> {
    SDLDisplay::pretty(self)
  }
}

impl<T: DisplaySDL + ?Sized> DisplaySDL for &T {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt(f)
  }

  #[inline(always)]
  fn fmt_compact(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt_compact(f)
  }

  #[inline(always)]
  fn fmt_pretty(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    (*self).fmt_pretty(f)
  }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum DisplayFmt {
  Compact,
  Pretty,
  #[default]
  Default,
}

/// A helper struct for displaying in a SDL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SDLDisplay<'a, T: ?Sized> {
  t: &'a T,
  fmt: DisplayFmt,
}

impl<T: DisplaySDL + ?Sized> core::fmt::Display for SDLDisplay<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self.fmt {
      DisplayFmt::Compact => self.t.fmt_compact(f),
      DisplayFmt::Pretty => self.t.fmt_pretty(f),
      DisplayFmt::Default => self.t.fmt(f),
    }
  }
}

impl<'a, T: ?Sized> SDLDisplay<'a, T> {
  /// Formats the value in a compact SDL.
  #[inline(always)]
  pub const fn compact(t: &'a T) -> Self {
    Self::with_fmt(t, DisplayFmt::Compact)
  }

  /// Formats the value in a pretty SDL.
  #[inline(always)]
  pub const fn pretty(t: &'a T) -> Self {
    Self::with_fmt(t, DisplayFmt::Pretty)
  }

  /// Formats the value in a default SDL.
  #[inline(always)]
  pub const fn default(t: &'a T) -> Self {
    Self::with_fmt(t, DisplayFmt::Default)
  }

  #[inline(always)]
  const fn with_fmt(t: &'a T, fmt: DisplayFmt) -> Self {
    Self { fmt, t }
  }
}
