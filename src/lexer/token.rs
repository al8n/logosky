use chumsky::{Parser, primitive::any};

use crate::{FromLexError, lexer::Require, require_token_parser_fn};

pub use logos::Logos;

/// Common kinds of token
pub mod kind;

/// An item produced by the lexer: either a recognized token `T` or a lexing error.
///
/// `Lexed` lets you keep errors *in* the stream so you can continue scanning and
/// report multiple diagnostics in one pass, or filter them out later.
#[derive(
  Debug,
  Clone,
  Copy,
  PartialEq,
  Eq,
  derive_more::IsVariant,
  derive_more::Unwrap,
  derive_more::TryUnwrap,
)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Lexed<'a, T: Token<'a>> {
  /// A successfully recognized token.
  Token(T),

  /// A lexing error produced while scanning.
  ///
  /// This usually contains enough information to render a diagnostic
  /// (e.g., span/byte range and an error kind/message).
  Error(T::Error),
}

impl<'a, T> core::fmt::Display for Lexed<'a, T>
where
  T: Token<'a>,
  T::Error: core::fmt::Display,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Token(tok) => ::core::fmt::Display::fmt(tok, f),
      Self::Error(err) => err.fmt(f),
    }
  }
}

impl<'a, T: Token<'a>> From<Result<T, T::Error>> for Lexed<'a, T> {
  #[inline(always)]
  fn from(value: Result<T, T::Error>) -> Self {
    match value {
      Ok(tok) => Self::Token(tok),
      Err(err) => Self::Error(err),
    }
  }
}

impl<'a, T: Token<'a>> From<Lexed<'a, T>> for Result<T, T::Error> {
  #[inline(always)]
  fn from(value: Lexed<'a, T>) -> Self {
    match value {
      Lexed::Token(tok) => Ok(tok),
      Lexed::Error(err) => Err(err),
    }
  }
}

/// The token trait.
pub trait Token<'a>: Logos<'a> + core::fmt::Debug + core::fmt::Display + 'a {}

impl<'a, T> Token<'a> for T where T: Logos<'a> + core::fmt::Debug + core::fmt::Display + 'a {}

require_token_parser_fn! {
  /// Returns a parser which parses a token and requires the parsed token to be of a specific specification.
  pub fn require_token<'a, I, E, Spec>(spec: Spec) -> Spec {
    any().try_map_with(move |tok: I::Token, exa| {
      tok.require(exa.slice(), exa.span(), spec)
        .map_err(|err| FromLexError::from_lex_error(err, exa.span()))
    })
  }

  /// Returns a parser which parse a whitespace token
  pub fn whitespace<'src, I, E>() -> kind::WhiteSpace {
    require_token(kind::WhiteSpace)
  }

  /// Returns a parser which parse a whitespaces token
  pub fn whitespaces<'src, I, E>() -> kind::WhiteSpaces {
    require_token(kind::WhiteSpaces)
  }

  /// Returns a parser which parse a line terminator token
  pub fn line_terminator<'src, I, E>() -> kind::LineTerminator {
    require_token(kind::LineTerminator)
  }

  /// Returns a parser which parse a comment token
  pub fn comment<'src, I, E>() -> kind::Comment {
    require_token(kind::Comment)
  }

  /// Returns a parser which parses many ignore tokens
  pub fn ignores<'src, I, E>() -> kind::Ignores {
    require_token(kind::Ignores)
  }

  /// Returns a parser which parse one ignore token
  pub fn ignore<'src, I, E>() -> kind::Ignore {
    require_token(kind::Ignore)
  }

  /// Returns a parser which parse an int token
  pub fn int<'src, I, E>() -> kind::IntLiteral {
    require_token(kind::IntLiteral)
  }

  /// Returns a parser which parses a float token
  pub fn float<'src, I, E>() -> kind::FloatLiteral {
    require_token(kind::FloatLiteral)
  }

  /// Returns a parser which parses a boolean token
  pub fn boolean<'src, I, E>() -> kind::BooleanLiteral {
    require_token(kind::BooleanLiteral)
  }

  /// Returns a parser which parses a null token
  pub fn null<'src, I, E>() -> kind::NullLiteral {
    require_token(kind::NullLiteral)
  }

  /// Returns a parser which parses an inline string token
  pub fn inline_string<'src, I, E>() -> kind::InlineStringLiteral {
    require_token(kind::InlineStringLiteral)
  }

  /// Returns a parser which parses a block string token
  pub fn block_string<'src, I, E>() -> kind::BlockStringLiteral {
    require_token(kind::BlockStringLiteral)
  }

  /// Returns a parser which parses a string token
  pub fn string<'src, I, E>() -> kind::StringLiteral {
    require_token(kind::StringLiteral)
  }

  /// Returns a parser which parsers an identifier token
  pub fn ident<'src, I, E>() -> kind::Ident {
    require_token(kind::Ident)
  }

  /// Returns a parser which parses a keyword token
  pub fn keyword<'src, I, E>(kw: &'src str) -> kind::Keyword<'src> {
    require_token(kind::Keyword(kw))
  }

  /// Returns a parser which parses an ASCII character token
  pub fn ascii<'src, I, E>(ch: kind::AsciiChar) -> kind::AsciiChar {
    require_token(ch)
  }

  /// Returns a parser which parsers a UTF-8 character token
  pub fn char<'src, I, E>(ch: char) -> char {
    require_token(ch)
  }
}
