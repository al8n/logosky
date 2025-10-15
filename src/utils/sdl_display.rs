mod sealed {
  pub trait Sealed {}

  impl<T: ?Sized + Sealed> Sealed for &T {}
}

/// A trait for displaying in a SDL.
///
/// This trait is not meant to be implemented outside of this crate.
/// Implementing [`DisplayCompact`] or [`DisplayPretty`], and use the [`CompactDisplay`] or [`PrettyDisplay`] wrappers,
/// which implement this trait.
pub trait DisplaySDL: sealed::Sealed {
  /// The options for SDL display.
  type Options: ?Sized;

  /// Formats the value in a SDL.
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result;

  /// Returns a wrapper which implement `Display`.
  fn display<'a>(&'a self, options: &'a Self::Options) -> impl core::fmt::Display + 'a;
}

impl<T: DisplaySDL + ?Sized> DisplaySDL for &T {
  type Options = T::Options;

  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result {
    <T as DisplaySDL>::fmt(*self, f, options)
  }

  fn display<'a>(&'a self, options: &'a Self::Options) -> impl core::fmt::Display + 'a {
    <T as DisplaySDL>::display(*self, options)
  }
}

/// A trait for displaying in a compact way.
pub trait DisplayCompact {
  /// The options for compact display.
  type Options: ?Sized;

  /// Formats the value in a compact way.
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result;

  /// Returns a wrapper which implement `Display` in a compact way.
  #[inline(always)]
  fn display<'a>(&'a self, options: &'a Self::Options) -> CompactDisplay<'a, Self> {
    CompactDisplay { t: self, options }
  }
}

impl<T: DisplayCompact + ?Sized> DisplayCompact for &T {
  type Options = T::Options;

  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result {
    (*self).fmt(f, options)
  }
}

/// A trait for displaying in a pretty way.
pub trait DisplayPretty {
  /// The options for pretty display.
  type Options: ?Sized;

  /// Formats the value in a pretty way.
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result;

  /// Returns a wrapper which implement `Display` in a pretty way.
  #[inline(always)]
  fn display<'a>(&'a self, options: &'a Self::Options) -> PrettyDisplay<'a, Self> {
    PrettyDisplay { t: self, options }
  }
}

impl<T: DisplayPretty + ?Sized> DisplayPretty for &T {
  type Options = T::Options;

  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result {
    (*self).fmt(f, options)
  }
}

/// A helper struct for displaying in a compact way.
pub struct CompactDisplay<'a, T: ?Sized + DisplayCompact> {
  t: &'a T,
  options: &'a T::Options,
}

impl<T> core::fmt::Display for CompactDisplay<'_, T>
where
  T: DisplayCompact + ?Sized,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.t.fmt(f, self.options)
  }
}

impl<T> sealed::Sealed for CompactDisplay<'_, T> where T: DisplayCompact + ?Sized {}

impl<T> DisplaySDL for CompactDisplay<'_, T>
where
  T: DisplayCompact + ?Sized,
{
  type Options = T::Options;

  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result {
    self.t.fmt(f, options)
  }

  #[inline(always)]
  fn display<'a>(&'a self, options: &'a Self::Options) -> impl core::fmt::Display + 'a {
    self.t.display(options)
  }
}

/// A helper struct for displaying in a pretty way.
pub struct PrettyDisplay<'a, T: ?Sized + DisplayPretty> {
  t: &'a T,
  options: &'a T::Options,
}

impl<T> core::fmt::Display for PrettyDisplay<'_, T>
where
  T: DisplayPretty + ?Sized,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.t.fmt(f, self.options)
  }
}

impl<T> sealed::Sealed for PrettyDisplay<'_, T> where T: DisplayPretty + ?Sized {}

impl<T> DisplaySDL for PrettyDisplay<'_, T>
where
  T: DisplayPretty + ?Sized,
{
  type Options = T::Options;

  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>, options: &Self::Options) -> core::fmt::Result {
    self.t.fmt(f, options)
  }

  #[inline(always)]
  fn display<'a>(&'a self, options: &'a Self::Options) -> impl core::fmt::Display + 'a {
    self.t.display(options)
  }
}
