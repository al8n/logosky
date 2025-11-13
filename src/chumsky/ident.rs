use crate::{IdentifierToken, error::UnexpectedIdentifier};

use super::*;

super::macros::builtin_expected_token_parser!(IdentifierToken {
  /// Returns a parser for any identifier token.
  ///
  /// Depends on how `T` implements [`IdentifierToken::is_identifier`](IdentifierToken::is_identifier).
  identifier,
});

/// Returns a parser that matches an identifier token satisfying the `raw` identifier.
pub fn expected_identifier<'a, 'e: 'a, I, T, Error, E>(
  raw: &'e str,
) -> impl Parser<'a, I, Spanned<T>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: IdentifierToken<'a>,
  str: Equivalent<<<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  Error: From<<T::Logos as Logos<'a>>::Error> + From<UnexpectedIdentifier<'e, T>> + 'a,
  E: ParserExtra<'a, I, Error = Error> + 'a,
{
  any().try_map(move |lexed: Lexed<'_, T>, span| match lexed {
    Lexed::Token(t) => {
      if t.data.matches_identifier(raw) {
        Ok(Spanned::new(span, t.data))
      } else {
        Err(<Error as core::convert::From<_>>::from(
          UnexpectedIdentifier::expected_one(span, t.data, raw),
        ))
      }
    }
    Lexed::Error(e) => Err(<Error as core::convert::From<_>>::from(e)),
  })
}
