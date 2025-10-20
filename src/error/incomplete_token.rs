use crate::utils::{Span, human_display::DisplayHuman};

/// An incomplete token
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IncompleteToken<Knowledge> {
  span: Span,
  knowledge: Option<Knowledge>,
}

impl<Knowledge> core::fmt::Display for IncompleteToken<Knowledge>
where
  Knowledge: DisplayHuman,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.knowledge {
      Some(knowledge) => write!(
        f,
        "incomplete {} token at {}",
        knowledge.display(),
        self.span
      ),
      None => write!(f, "incomplete token at {}", self.span),
    }
  }
}

impl<Knowledge> core::error::Error for IncompleteToken<Knowledge> where
  Knowledge: DisplayHuman + core::fmt::Debug
{
}

impl<Knowledge> IncompleteToken<Knowledge> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  const fn new_in(span: Span, knowledge: Option<Knowledge>) -> Self {
    Self { span, knowledge }
  }

  /// Create a new IncompleteToken knowledge from a Span
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(span: Span) -> Self {
    Self::new_in(span, None)
  }

  /// Create a new IncompleteToken knowledge from a Span and Knowledge
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_knowledge(span: Span, knowledge: Knowledge) -> Self {
    Self::new_in(span, Some(knowledge))
  }

  /// Get the span of the incomplete knowledge
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    self.span
  }

  /// Get the knowledge of the incomplete knowledge, if any
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn knowledge(&self) -> Option<&Knowledge> {
    self.knowledge.as_ref()
  }

  /// Decompose the IncompleteToken knowledge into its components
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_components(self) -> (Span, Option<Knowledge>) {
    (self.span, self.knowledge)
  }

  /// Bumps both the start and end positions of the span by the given offset.
  ///
  /// This is useful when adjusting error positions after processing or
  /// when combining spans from different contexts.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn bump(&mut self, offset: usize) {
    self.span.bump(offset);
  }
}
