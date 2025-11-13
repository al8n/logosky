use super::*;

pub use ident::*;
pub use lit::*;

/// Operator parsers
pub mod operator;
/// Puncatuator parsers
pub mod punct;

/// Identifier parsers
mod ident;
/// Lit token parsers
mod lit;

mod macros;

macros::builtin_expected_token_parser!(KeywordToken {
  /// Returns a parser for any keyword token.
  ///
  /// Depends on how `T` implements [`KeywordToken::is_keyword`](KeywordToken::is_keyword).
  keyword,
});

/// Returns a parser that matches a specific keyword token.
///
/// # Example
///
/// ```rust,ignore
/// use logosky::{chumsky::{keyword, LogoStream, prelude::*}, Tokenizer};
///
/// enum SyntaxKind {
///   if_KW,
///   // ...
/// }
///
/// let parser = expected_keyword("if", || SyntaxKind::if_KW);
/// ```
pub fn expected_keyword<'a, 'e: 'a, I, T, Error, E>(
  raw: &'e str,
) -> impl Parser<'a, I, Spanned<T>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: KeywordToken<'a>,
  str: Equivalent<T>,
  Error: From<<T::Logos as Logos<'a>>::Error> + From<UnexpectedKeyword<'e, T>> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().try_map(move |lexed: Lexed<'_, T>, span| match lexed {
    Lexed::Token(t) => {
      if Equivalent::equivalent(raw, &t.data) {
        Ok(Spanned::new(span, t.data))
      } else {
        Err(<Error as core::convert::From<_>>::from(
          UnexpectedKeyword::expected_one(span, t.data, raw),
        ))
      }
    }
    Lexed::Error(e) => Err(<Error as core::convert::From<_>>::from(e)),
  })
}

/// Returns a parser that matches a token satisfying a predicate.
pub fn expected_token<'a, 'e: 'a, I, T, Exp, Error, E>(
  f: impl Fn(&T) -> bool + Clone + 'a,
  expected: impl Fn() -> Expected<'e, Exp> + Clone + 'a,
) -> impl Parser<'a, I, Spanned<T>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  Exp: 'e,
  Error: From<<T::Logos as Logos<'a>>::Error> + From<UnexpectedToken<'e, T, Exp>> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().try_map(move |lexed: Lexed<'_, T>, span| match lexed {
    Lexed::Token(t) => {
      if f(&t.data) {
        Ok(Spanned::new(span, t.data))
      } else {
        let e = UnexpectedToken::new(span, expected()).with_found(t.data);
        Err(<Error as core::convert::From<_>>::from(e))
      }
    }
    Lexed::Error(e) => Err(<Error as core::convert::From<_>>::from(e)),
  })
}

/// Returns a parser that validate a token and map, producing non-terminal errors if it does not fulfill certain criteria
///
/// If the token yields an error, the parser emits the error and returns `None`.
pub fn validate_and_try_map_token<'a, I, T, O, Error, E>(
  f: impl Fn(Spanned<T>) -> Result<O, Error> + Clone + 'a,
) -> impl Parser<'a, I, Option<O>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().validate(move |lexed: Lexed<'_, T>, _, emitter| match lexed {
    Lexed::Token(t) => match f(t) {
      Ok(o) => Some(o),
      Err(e) => {
        emitter.emit(e);
        None
      }
    },
    Lexed::Error(e) => {
      emitter.emit(<Error as core::convert::From<_>>::from(e));
      None
    }
  })
}

/// Returns a parser that validate a token and map, producing non-terminal errors if it does not fulfill certain criteria
///
/// If the token yields an error, the parser emits the error and returns `None`.
pub fn validate_and_map_token<'a, I, T, O, Error, E>(
  f: impl Fn(Spanned<T>) -> O + Clone + 'a,
) -> impl Parser<'a, I, Option<O>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().validate(move |lexed: Lexed<'_, T>, _, emitter| match lexed {
    Lexed::Token(t) => Some(f(t)),
    Lexed::Error(e) => {
      emitter.emit(<Error as core::convert::From<_>>::from(e));
      None
    }
  })
}

/// Returns a parser that tries to map a token
pub fn try_map_token<'a, I, T, O, Error, E>(
  f: impl Fn(Spanned<T>) -> Result<O, Error> + Clone + 'a,
) -> impl Parser<'a, I, O, E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().try_map(move |lexed: Lexed<'_, T>, _| match lexed {
    Lexed::Token(t) => match f(t) {
      Ok(o) => Ok(o),
      Err(e) => Err(e),
    },
    Lexed::Error(e) => Err(<Error as core::convert::From<_>>::from(e)),
  })
}

/// Returns a parser that maps a token
///
/// If the token yields an error, the parser emits the error and returns `None`.
pub fn map_token<'a, I, T, O, Error, E>(
  f: impl Fn(Spanned<T>) -> O + Clone + 'a,
) -> impl Parser<'a, I, O, E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().try_map(move |lexed: Lexed<'_, T>, _| match lexed {
    Lexed::Token(t) => Ok(f(t)),
    Lexed::Error(e) => Err(<Error as core::convert::From<_>>::from(e)),
  })
}
