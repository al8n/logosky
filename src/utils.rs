use core::ops::Range;

pub use human_display::*;
pub use positioned_char::*;
pub use unexpected_end::*;
pub use unexpected_lexeme::*;

mod human_display;
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
