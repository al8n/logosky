use core::ops::Range;

pub use positioned_char::*;
pub use unexpected_end::*;
pub use unexpected_lexeme::*;

/// Trackers for preventing infinite recursion in parsers.
pub mod recursion_tracker;
/// A token tracker for tracking tokens in a lexer.
pub mod token_tracker;
/// A tracker for tracking recursion depth and tokens.
pub mod tracker;

/// A module for displaying in a human-friendly way.
pub mod human_display;
/// A module for displaying in SDL.
pub mod sdl_display;
/// A module for displaying in syntax trees.
pub mod syntax_tree_display;

/// A module for container types with small size optimizations.
#[cfg(feature = "smallvec")]
#[cfg_attr(docsrs, doc(cfg(feature = "smallvec")))]
pub mod container;

mod positioned_char;
mod unexpected_end;
mod unexpected_lexeme;

/// A simple span just contains start and end position.
///
/// The structure is the same as [`Range<usize>`], but with more friendly methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
  start: usize,
  end: usize,
}

impl chumsky::span::Span for Span {
  type Context = ();

  type Offset = usize;

  #[inline(always)]
  fn new(_: Self::Context, range: Range<Self::Offset>) -> Self {
    Self::new(range.start, range.end)
  }

  #[inline(always)]
  fn context(&self) -> Self::Context {}

  #[inline(always)]
  fn start(&self) -> Self::Offset {
    self.start
  }

  #[inline(always)]
  fn end(&self) -> Self::Offset {
    self.end
  }
}

impl Span {
  /// Create a new span.
  ///
  /// ## Panics
  ///
  /// Panics if `end < start`.
  #[inline]
  pub const fn new(start: usize, end: usize) -> Self {
    assert!(end >= start, "end must be greater than or equal to start");
    Self { start, end }
  }

  /// Try to create a new span.
  ///
  /// Returns `None` if `end < start`.
  #[inline]
  pub const fn try_new(start: usize, end: usize) -> Option<Self> {
    if end >= start {
      Some(Self { start, end })
    } else {
      None
    }
  }

  /// Bump the start of the span by `n`.
  ///
  /// ## Panics
  ///
  /// Panics if `self.start + n > self.end`.
  #[inline]
  pub const fn bump_start(&mut self, n: usize) -> &mut Self {
    self.start += n;
    assert!(
      self.start <= self.end,
      "start must be less than or equal to end"
    );
    self
  }

  /// Bump the end of the span by `n`.
  #[inline]
  pub const fn bump_end(&mut self, n: usize) -> &mut Self {
    self.end += n;
    self
  }

  /// Bump the start and the end of the span by `n`.
  #[inline]
  pub const fn bump_span(&mut self, n: usize) -> &mut Self {
    self.start += n;
    self.end += n;
    self
  }

  /// Set the start of the span, returning a mutable reference to self.
  #[inline]
  pub const fn set_start(&mut self, start: usize) -> &mut Self {
    self.start = start;
    self
  }

  /// Set the end of the span, returning a mutable reference to self.
  #[inline]
  pub const fn set_end(&mut self, end: usize) -> &mut Self {
    self.end = end;
    self
  }

  /// Set the start of the span, returning self.
  #[inline]
  pub const fn with_start(mut self, start: usize) -> Self {
    self.start = start;
    self
  }

  /// Set the end of the span, returning self.
  #[inline]
  pub const fn with_end(mut self, end: usize) -> Self {
    self.end = end;
    self
  }

  /// Get the start of the span.
  #[inline]
  pub const fn start(&self) -> usize {
    self.start
  }

  /// Get the mutable reference to the start of the span.
  #[inline]
  pub const fn start_mut(&mut self) -> &mut usize {
    &mut self.start
  }

  /// Get the end of the span.
  #[inline]
  pub const fn end(&self) -> usize {
    self.end
  }

  /// Get the mutable reference to the end of the span.
  #[inline]
  pub const fn end_mut(&mut self) -> &mut usize {
    &mut self.end
  }

  /// Get the length of the span.
  #[inline]
  pub const fn len(&self) -> usize {
    self.end - self.start
  }

  /// Check if the span is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.start == self.end
  }

  /// Returns a range covering the span.
  #[inline]
  pub const fn range(&self) -> Range<usize> {
    self.start..self.end
  }
}

impl From<Range<usize>> for Span {
  #[inline]
  fn from(range: Range<usize>) -> Self {
    Self::new(range.start, range.end)
  }
}

impl From<Span> for Range<usize> {
  #[inline]
  fn from(span: Span) -> Self {
    span.start..span.end
  }
}

/// A spanned value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Spanned<D> {
  /// The span of the data.
  pub span: Span,
  /// The spanned data.
  pub data: D,
}

impl<D> core::fmt::Display for Spanned<D>
where
  D: core::fmt::Display,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.data.fmt(f)
  }
}

impl<D> Spanned<D> {
  /// Create a new spanned value.
  #[inline]
  pub(super) const fn new(span: Span, data: D) -> Self {
    Self { span, data }
  }

  /// Get a reference to the span.
  #[inline]
  pub const fn span(&self) -> &Span {
    &self.span
  }

  /// Get a mutable reference to the span.
  #[inline]
  pub const fn span_mut(&mut self) -> &mut Span {
    &mut self.span
  }

  /// Get a reference to the data.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }

  /// Get a mutable reference to the data.
  #[inline]
  pub const fn data_mut(&mut self) -> &mut D {
    &mut self.data
  }

  /// Returns a reference to the span and data.
  #[inline]
  pub const fn as_ref(&self) -> Spanned<&D> {
    Spanned {
      span: self.span,
      data: &self.data,
    }
  }

  /// Consume the spanned value and return the data.
  #[inline]
  pub fn into_data(self) -> D {
    self.data
  }

  /// Decompose the spanned value into its span and data.
  #[inline]
  pub fn into_components(self) -> (Span, D) {
    (self.span, self.data)
  }
}
