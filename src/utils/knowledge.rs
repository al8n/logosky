use derive_more::{Display, IsVariant};

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

/// A displayable hex literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("hex literal")]
pub struct HexLiteral(pub(crate) ());

impl DisplayHuman for HexLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}

/// A displayable binary literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("binary literal")]
pub struct BinaryLiteral(pub(crate) ());

impl DisplayHuman for BinaryLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}

/// A displayable octal literal description.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
#[display("octal literal")]
pub struct OctalLiteral(pub(crate) ());

impl DisplayHuman for OctalLiteral {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    ::core::fmt::Display::fmt(self, f)
  }
}

/// An enumeration of line terminator types.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, IsVariant, Display)]
pub enum LineTerminator {
  /// A newline character (`\n`).
  #[display("\\n")]
  NewLine,
  /// A carriage return character (`\r`).
  #[display("\\r")]
  CarriageReturn,
  /// A carriage return followed by a newline (`\r\n`).
  #[display("\\r\\n")]
  CarriageReturnNewLine,
}
