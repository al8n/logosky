use super::{Span, human_display::DisplayHuman};

/// A malformed literal token
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MalformedLiteral<Knowledge> {
  span: Span,
  knowledge: Option<Knowledge>,
}

impl<Knowledge> core::fmt::Display for MalformedLiteral<Knowledge>
where
  Knowledge: DisplayHuman,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match &self.knowledge {
      Some(knowledge) => write!(
        f,
        "malformed literal at {}, did you mean {}?",
        self.span,
        knowledge.display()
      ),
      None => write!(f, "malformed literal at {}", self.span),
    }
  }
}

impl<Knowledge> core::error::Error for MalformedLiteral<Knowledge> where
  Knowledge: DisplayHuman + core::fmt::Debug
{
}

impl<Knowledge> MalformedLiteral<Knowledge> {
  /// Create a new MalformedLiteral knowledge from a Span
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(span: Span) -> Self {
    Self {
      span,
      knowledge: None,
    }
  }

  /// Create a new MalformedLiteral knowledge from a Span and Knowledge
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_knowledge(span: Span, knowledge: Knowledge) -> Self {
    Self {
      span,
      knowledge: Some(knowledge),
    }
  }

  /// Get the span of the malformed literal knowledge
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn span(&self) -> Span {
    self.span
  }

  /// Get the knowledge of the malformed literal knowledge, if any
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn knowledge(&self) -> Option<&Knowledge> {
    self.knowledge.as_ref()
  }

  /// Consume self and return the span and knowledge
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
