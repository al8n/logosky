/// Generates parsers fn that match expected tokens with custom error messages.
///
/// # Example
///
/// ```rust,ignore
/// use logosky::chumsky::{expected_token_parser, LogoStream, prelude::*};
///
/// enum SyntaxKind {
///  Identifier,
/// // ...
/// }
///
/// expected_token_parser! {
///   /// Parses an identifier token.
///   fn identifier(|t: &Token| matches!(t, Token::Identifier(_)));
/// }
/// ```
#[macro_export]
macro_rules! expected_token_parser {
  ($(
    $(#[$meta:meta])*
    $vis:vis fn $name:ident($fn:expr)
  );+$(;)?) => {
    $crate::__private::paste::paste! {
      $(
        $(#[$meta])*
        $vis fn $name<'a, 'e: 'a, I, T, K, Error, E>(
          expected: impl ::core::ops::Fn() -> $crate::__private::utils::Expected<'e, K> + ::core::clone::Clone + 'a,
        ) -> impl $crate::__private::chumsky::Parser<'a, I, $crate::__private::utils::Spanned<T>, E> + ::core::clone::Clone
        where
          I: $crate::__private::LogoStream<'a, T>,
          T: $crate::__private::Token<'a>,
          K: 'e,
          Error: ::core::convert::From<<T::Logos as $crate::__private::logos::Logos<'a>>::Error> + ::core::convert::From<$crate::__private::error::UnexpectedEot> + ::core::convert::From<$crate::__private::error::UnexpectedToken<'e, T, K>> + 'a,
          E: $crate::__private::chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
        {
          $crate::__private::chumsky::expected_token(
            $fn,
            expected,
          )
        }
      )*
    }
  };
}

macro_rules! builtin_expected_token_parser {
  ($trait:ident {
    $(
      $(#[$meta:meta])*
      $name:ident
    ),+$(,)?
  }) => {
    $crate::__private::paste::paste! {
      $(
        $(#[$meta])*
        pub fn $name<'a, 'e: 'a, I, T, K, Error, E>(
          expected: impl ::core::ops::Fn() -> K + ::core::clone::Clone + 'a,
        ) -> impl $crate::__private::chumsky::Parser<'a, I, $crate::__private::utils::Spanned<T>, E> + ::core::clone::Clone
        where
          I: $crate::__private::LogoStream<'a, T>,
          T: $crate::__private::$trait<'a>,
          K: 'e,
          Error: ::core::convert::From<<T::Logos as $crate::__private::logos::Logos<'a>>::Error> + ::core::convert::From<$crate::__private::error::UnexpectedEot> + ::core::convert::From<$crate::__private::error::UnexpectedToken<'e, T, K>> + 'a,
          E: $crate::__private::chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
        {
          $crate::__private::chumsky::expected_token(
            <T as $crate::__private::$trait<'a>>::[< is_ $name >],
            move || $crate::__private::utils::Expected::One(expected()),
          )
        }
      )*
    }
  };
}

pub(super) use builtin_expected_token_parser;
