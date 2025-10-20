use derive_more::{Display, IsVariant};

/// `{}` delimiters.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Brace;

/// `()` delimiters.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Paren;

/// `[]` delimiters.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bracket;

/// `<>` delimiters.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Angle;

/// Common delimiters used in lexing and parsing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, IsVariant, Display)]
pub enum Delimiter {
  /// `{` and `}` delimiters.
  #[display("{{}}")]
  Brace,
  /// `(` and `)` delimiters.
  #[display("()")]
  Paren,
  /// `[` and `]` delimiters.
  #[display("[]")]
  Bracket,
  /// `<` and `>` delimiters.
  #[display("<>")]
  Angle,
}
