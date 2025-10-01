use derive_more::{IsVariant, TryUnwrap, Unwrap};
use logos::Lexer;

use crate::{
  TokenStream,
  utils::{Span, Spanned},
};

pub use logos::Logos;

/// Common kinds of token
pub mod kind;

/// An item produced by the lexer: either a recognized token `T` or a lexing error.
///
/// `Lexed` lets you keep errors *in* the stream so you can continue scanning and
/// report multiple diagnostics in one pass, or filter them out later.
#[derive(Debug, PartialEq, IsVariant, Unwrap, TryUnwrap)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Lexed<'a, T: Token<'a>> {
  /// A successfully recognized token.
  Token(Spanned<T>),

  /// A lexing error produced while scanning.
  ///
  /// This usually contains enough information to render a diagnostic
  /// (e.g., span/byte range and an error kind/message).
  Error(<T::Logos as Logos<'a>>::Error),
}

impl<'a, T> Clone for Lexed<'a, T>
where
  T: Token<'a>,
{
  #[inline(always)]
  fn clone(&self) -> Self {
    match self {
      Self::Token(tok) => Self::Token(tok.clone()),
      Self::Error(err) => Self::Error(err.clone()),
    }
  }
}

impl<'a, T> Copy for Lexed<'a, T>
where
  T: Token<'a> + Copy,
  <T::Logos as Logos<'a>>::Error: Copy,
{
}

impl<'a, T: Token<'a>> Lexed<'a, T> {
  /// Lexes the next token from the given lexer, returning `None` if the input is exhausted.
  #[inline(always)]
  pub fn lex(lexer: &mut Lexer<'a, T::Logos>) -> Option<Self> {
    lexer.next().map(|res| {
      let span = lexer.span();
      res
        .map(|tok| (crate::utils::Span::from(span), T::from(tok)))
        .into()
    })
  }
}

impl<'a, T: 'a> core::fmt::Display for Lexed<'a, T>
where
  T: Token<'a> + core::fmt::Display,
  <T::Logos as Logos<'a>>::Error: core::fmt::Display,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Token(tok) => ::core::fmt::Display::fmt(tok, f),
      Self::Error(err) => err.fmt(f),
    }
  }
}

impl<'a, T: Token<'a>> From<Result<(Span, T), <T::Logos as Logos<'a>>::Error>> for Lexed<'a, T> {
  #[inline(always)]
  fn from(value: Result<(Span, T), <T::Logos as Logos<'a>>::Error>) -> Self {
    match value {
      Ok((span, tok)) => Self::Token(Spanned::new(span, tok)),
      Err(err) => Self::Error(err),
    }
  }
}

impl<'a, T: Token<'a>> From<Lexed<'a, T>> for Result<T, <T::Logos as Logos<'a>>::Error> {
  #[inline(always)]
  fn from(value: Lexed<'a, T>) -> Self {
    match value {
      Lexed::Token(tok) => Ok(tok.into_data()),
      Lexed::Error(err) => Err(err),
    }
  }
}

/// The token trait.
pub trait Token<'a>: Clone + core::fmt::Debug + From<Self::Logos> + 'a {
  /// The character type of the token.
  type Char: Copy + core::fmt::Debug + PartialEq + Eq + core::hash::Hash;
  /// The kind type of the token.
  type Kind: Copy + core::fmt::Debug + PartialEq + Eq + core::hash::Hash;
  /// The logos
  type Logos: Logos<'a> + Clone;

  /// Returns the kind of the token.
  fn kind(&self) -> Self::Kind;
}

/// The token extension trait.
pub trait TokenExt<'a>: Token<'a> {
  /// Returns a lexer for the token type from the given input.
  #[inline(always)]
  fn lexer(input: &'a <Self::Logos as Logos<'a>>::Source) -> TokenStream<'a, Self>
  where
    <Self::Logos as Logos<'a>>::Extras: Default,
  {
    TokenStream::new(input)
  }

  /// Returns a lexer for the token type from the given input.
  #[inline(always)]
  fn lexer_with_state(
    input: &'a <Self::Logos as Logos<'a>>::Source,
    state: <Self::Logos as Logos<'a>>::Extras,
  ) -> TokenStream<'a, Self> {
    TokenStream::with_state(input, state)
  }

  /// Lexes the next token from the given lexer, returning `None` if the input is exhausted.
  #[inline(always)]
  fn lex(lexer: &mut Lexer<'a, Self::Logos>) -> Option<Lexed<'a, Self>> {
    Lexed::lex(lexer)
  }
}

impl<'a, T> TokenExt<'a> for T where T: Token<'a> {}
