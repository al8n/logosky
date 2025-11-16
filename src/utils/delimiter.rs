use derive_more::{Display, IsVariant};

use crate::DelimiterToken;

/// `{`.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("{{")]
pub struct LBrace;

/// `}`.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("}}")]
pub struct RBrace;

/// `{}` delimiters.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("{{}}")]
pub struct Brace;

/// `(`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("(")]
pub struct LParen;

/// `)`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(")")]
pub struct RParen;

/// `()` delimiters.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("()")]
pub struct Paren;

/// `[`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("[")]
pub struct LBracket;

/// `]`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("]")]
pub struct RBracket;

/// `[]` delimiters.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("[]")]
pub struct Bracket;

/// `<`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("<")]
pub struct LAngle;

/// `>`
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display(">")]
pub struct RAngle;

/// `<>` delimiters.
#[derive(Debug, Default, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[display("<>")]
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

impl Delimiter {
  /// Returns `true` if the given token is an opening delimiter of this kind.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn is_open<'a, T: DelimiterToken<'a>>(&self, token: &T) -> bool {
    match self {
      Delimiter::Brace => token.is_brace_open(),
      Delimiter::Paren => token.is_paren_open(),
      Delimiter::Bracket => token.is_bracket_open(),
      Delimiter::Angle => token.is_angle_open(),
    }
  }

  /// Returns `true` if the given token is a closing delimiter of this kind.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn is_close<'a, T: DelimiterToken<'a>>(&self, token: &T) -> bool {
    match self {
      Delimiter::Brace => token.is_brace_close(),
      Delimiter::Paren => token.is_paren_close(),
      Delimiter::Bracket => token.is_bracket_close(),
      Delimiter::Angle => token.is_angle_close(),
    }
  }
}
