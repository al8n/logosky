use derive_more::Display;

use super::human_display::DisplayHuman;

/// A displayable hex float literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("hex float literal")]
pub struct HexFloatLiteral(pub(crate) ());

impl DisplayHuman for HexFloatLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}

/// A displayable float literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("float literal")]
pub struct FloatLiteral(pub(crate) ());

impl DisplayHuman for FloatLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}

/// A displayable int literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("int literal")]
pub struct IntLiteral(pub(crate) ());

impl DisplayHuman for IntLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}
