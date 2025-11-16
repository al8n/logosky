use core::{fmt, marker::PhantomData};

use crate::{
  syntax::{Language, Syntax},
  utils::Span,
};

/// Describes a missing syntax element between two anchors.
///
/// `Missing<T, Lang>` remembers the span immediately **before** the missing syntax and,
/// optionally, the span immediately **after** it. This allows diagnostics to highlight the
/// precise gap where the parser expected a `T` node. The generic `T` refers to a
/// [`Syntax`] implementation so the error can report the exact syntax kind via
/// [`Syntax::KIND`], while `Lang` ties the error to a specific [`Language`].
///
/// # When to Use
///
/// - A required AST/CST node is completely absent (e.g., missing identifier or block)
/// - Delimited structures contain consecutive items without the expected syntax between them
/// - Recovery wants to surface “something should be here” while pointing to the surrounding
///   context instead of fabricating bogus spans
///
/// # Anchors
///
/// - **`before`**: Span of the last token confidently parsed before the missing node.
/// - **`after` (optional)**: Span of the first token parsed after the missing node.
///   When `after` is `None` the gap is assumed to be at end-of-input or before an unknown
///   boundary.
///
/// The [`span`](Self::span) method derives a zero-width span when only `before` is known, or
/// the exclusive range between `before.end()` and `after.start()` when both anchors exist.
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::{
///     error::Missing,
///     syntax::{Language, Syntax},
///     utils::Span,
/// };
///
/// // Suppose `ParameterListSyntax` implements `Syntax<KIND = SyntaxKind::ParameterList>`
/// let before = Span::new(10, 11); // '('
/// let after = Span::new(12, 13);  // ')'
/// let error = Missing::<ParameterListSyntax, MyLang>::between(before, after);
///
/// assert_eq!(error.kind(), SyntaxKind::ParameterList);
/// assert_eq!(error.span(), Span::new(11, 12)); // gap between '(' and ')'
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Missing<T, Lang> {
  before: Span,
  after: Option<Span>,
  _syntax: PhantomData<T>,
  _lang: PhantomData<Lang>,
}

impl<T, Lang> Missing<T, Lang> {
  /// Creates a missing error that occurs **after** the provided span.
  ///
  /// Use this when the parser reached the end of a construct without finding the required
  /// syntax (e.g., missing trailing expression before `}` or end-of-input).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(before: Span) -> Self {
    Self {
      before,
      after: None,
      _syntax: PhantomData,
      _lang: PhantomData,
    }
  }

  /// Creates a missing error bounded by both a `before` and `after` span.
  ///
  /// The resulting [`span`](Self::span) covers the gap between `before.end()` and
  /// `after.start()`. When the anchors overlap (e.g., consecutive tokens), the gap collapses
  /// to a zero-width span at `after.start()`.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn between(before: Span, after: Span) -> Self {
    Self {
      before,
      after: Some(after),
      _syntax: PhantomData,
      _lang: PhantomData,
    }
  }

  /// Updates the trailing anchor, returning `self` for chaining.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_after(mut self, after: Span) -> Self {
    self.after = Some(after);
    self
  }

  /// Sets/overwrites the trailing anchor in-place.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn set_after(&mut self, after: Span) {
    self.after = Some(after);
  }

  /// Returns the span immediately preceding the missing syntax.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn before(&self) -> Span {
    self.before
  }

  /// Returns the optional span immediately following the missing syntax.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn after(&self) -> Option<Span> {
    self.after
  }

  /// Returns the span representing the gap where the syntax should have existed.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    Self::gap_span(self.before, self.after)
  }

  /// Returns the syntax kind of the missing node.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn kind(&self) -> <Lang as Language>::SyntaxKind
  where
    T: Syntax<Lang = Lang>,
    Lang: Language,
  {
    T::KIND
  }

  const fn gap_span(before: Span, after: Option<Span>) -> Span {
    match after {
      Some(after_span) => {
        let start = before.end();
        let end = after_span.start();

        if end >= start {
          Span::new(start, end)
        } else {
          Span::new(end, end)
        }
      }
      None => {
        let pos = before.end();
        Span::new(pos, pos)
      }
    }
  }
}

impl<T, Lang> fmt::Display for Missing<T, Lang>
where
  T: Syntax<Lang = Lang>,
  Lang: Language,
  <Lang as Language>::SyntaxKind: fmt::Display,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.after {
      Some(after) => write!(
        f,
        "missing {} between {} and {}",
        self.kind(),
        self.before,
        after
      ),
      None => write!(f, "missing {} after {}", self.kind(), self.before),
    }
  }
}

impl<T, Lang> fmt::Debug for Missing<T, Lang>
where
  T: Syntax<Lang = Lang>,
  Lang: Language,
  <Lang as Language>::SyntaxKind: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Missing")
      .field("kind", &self.kind())
      .field("before", &self.before)
      .field("after", &self.after)
      .finish()
  }
}

impl<T, Lang> core::error::Error for Missing<T, Lang>
where
  T: Syntax<Lang = Lang>,
  Lang: Language,
  <Lang as Language>::SyntaxKind: fmt::Display + fmt::Debug,
{
}
