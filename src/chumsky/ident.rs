use crate::IdentifierToken;

use super::*;

super::macros::builtin_expected_token_parser!(IdentifierToken {
  /// Returns a parser for any identifier token.
  ///
  /// Depends on how `T` implements [`IdentifierToken::is_identifier`](IdentifierToken::is_identifier).
  identifier,
});

/// Returns a parser that matches an identifier token satisfying the `raw` identifier.
pub fn expected_identifier<'a, 'e: 'a, I, T, Exp, Error, E>(
  raw: &'a str,
  expected: impl Fn() -> Exp + Clone + 'a,
) -> impl Parser<'a, I, Spanned<T>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: IdentifierToken<'a>,
  str: Equivalent<<<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  Exp: 'e,
  Error: From<<T::Logos as Logos<'a>>::Error> + From<UnexpectedToken<'e, T, Exp>> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  expected_token(
    |t: &T| t.matches_identifier(raw),
    move || Expected::One(expected()),
  )
}
