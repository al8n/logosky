super::macros::builtin_expected_token_parser!(OperatorToken {
  /// Returns a parser for the assign operator, e.g., `=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_eq_assign`](crate::lexer::OperatorToken::is_eq_assign).
  eq_assign,
  /// Returns a parser for the colon assign operator, e.g., `:=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_colon_eq_assign`](crate::lexer::OperatorToken::is_colon_eq_assign).
  colon_eq_assign,
  /// Returns a parser for the add operator, e.g., `+`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_add`](crate::lexer::OperatorToken::is_add).
  add,
  /// Returns a parser for the add assign operator, e.g., `+=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_add_assign`](crate::lexer::OperatorToken::is_add_assign).
  add_assign,
  /// Returns a parser for the minus operator, e.g., `-`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_sub`](crate::lexer::OperatorToken::is_sub).
  sub,
  /// Returns a parser for the subtract assign operator, e.g., `-=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_sub_assign`](crate::lexer::OperatorToken::is_sub_assign).
  sub_assign,
  /// Returns a parser for the multiply operator, e.g., `*`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_mul`](crate::lexer::OperatorToken::is_mul).
  mul,
  /// Returns a parser for the multiply assign operator, e.g., `*=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_mul_assign`](crate::lexer::OperatorToken::is_mul_assign).
  mul_assign,
  /// Returns a parser for the divide operator, e.g., `/`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_div`](crate::lexer::OperatorToken::is_div).
  div,
  /// Returns a parser for the divide assign operator, e.g., `/=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_div_assign`](crate::lexer::OperatorToken::is_div_assign).
  div_assign,
  /// Returns a parser for the power operator, e.g., `**`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_pow`](crate::lexer::OperatorToken::is_pow).
  pow,
  /// Returns a parser for the power assign operator, e.g., `**=`.
  /// Depends on how `T` implements [`OperatorToken::is_pow_assign`](crate::lexer::OperatorToken::is_pow_assign).
  pow_assign,
  /// Returns a paser for the modulo assign operator, e.g., `%=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_mod_assign`](crate::lexer::OperatorToken::is_mod_assign).
  mod_assign,

  /// Returns a parser for the bitadd operator, e.g., `&`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitand`](crate::lexer::OperatorToken::is_bitand).
  bitand,
  /// Returns a parser for the bitand assign operator, e.g., `&=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitand_assign`](crate::lexer::OperatorToken::is_bitand_assign).
  bitand_assign,

  /// Returns a parser for the bitor operator, e.g., `|`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitor`](crate::lexer::OperatorToken::is_bitor).
  bitor,
  /// Returns a parser for the bitor assign operator, e.g., `|=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitor_assign`](crate::lexer::OperatorToken::is_bitor_assign).
  bitor_assign,
  /// Returns a parser for the bitxor operator, e.g., `^`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitxor`](crate::lexer::OperatorToken::is_bitxor).
  bitxor,
  /// Returns a parser for the bitxor assign operator, e.g., `^=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_bitxor_assign`](crate::lexer::OperatorToken::is_bitxor_assign).
  bitxor_assign,
  /// Returns a parser for the increment operator, e.g., `++`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_increment`](crate::lexer::OperatorToken::is_increment).
  increment,
  /// Returns a parser for the decrement operator, e.g., `--`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_decrement`](crate::lexer::OperatorToken::is_decrement).
  decrement,
  /// Returns a parser for the logical XOR operator, e.g., `^^`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_xor`](crate::lexer::OperatorToken::is_logical_xor).
  logical_xor,
  /// Returns a parser for the logical AND operator, e.g., `&&`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_and`](crate::lexer::OperatorToken::is_logical_and).
  logical_and,
  /// Returns a parser for the logical OR operator, e.g., `||`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_or`](crate::lexer::OperatorToken::is_logical_or).
  logical_or,
  /// Returns a parser for the logical NOT operator, e.g., `!`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_not`](crate::lexer::OperatorToken::is_logical_not).
  logical_not,
  /// Returns a parser for the equal operator, e.g., `==`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_eq`](crate::lexer::OperatorToken::is_eq).
  eq,
  /// Returns a parser for the not equal operator, e.g., `!=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_ne`](crate::lexer::OperatorToken::is_ne).
  ne,
  /// Returns a parser for the strict equal operator, e.g., `===`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_eq`](crate::lexer::OperatorToken::is_strict_eq).
  strict_eq,
  /// Returns a parser for the strict not equal operator, e.g., `!==`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_ne`](crate::lexer::OperatorToken::is_strict_ne).
  strict_ne,
  /// Returns a parser for the less than operator, e.g., `<`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_lt`](crate::lexer::OperatorToken::is_lt).
  lt,
  /// Returns a parser for the strict less than operator, e.g., `<`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_lt`](crate::lexer::OperatorToken::is_strict_lt).
  strict_lt,
  /// Returns a parser for the less than or equal to operator, e.g., `<=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_le`](crate::lexer::OperatorToken::is_le).
  le,
  /// Returns a parser for the strict less than or equal to operator, e.g., `<=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_le`](crate::lexer::OperatorToken::is_strict_le).
  strict_le,
  /// Returns a parser for the greater than operator, e.g., `>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_gt`](crate::lexer::OperatorToken::is_gt).
  gt,
  /// Returns a parser for the strict greater than operator, e.g., `>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_gt`](crate::lexer::OperatorToken::is_strict_gt).
  strict_gt,
  /// Returns a parser for the greater than or equal to operator, e.g., `>=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_ge`](crate::lexer::OperatorToken::is_ge).
  ge,
  /// Returns a parser for the strict greater than or equal to operator, e.g., `>=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_ge`](crate::lexer::OperatorToken::is_strict_ge).
  strict_ge,
  /// Returns a parser for the left shift operator, e.g., `<<`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shl`](crate::lexer::OperatorToken::is_shl).
  shl,
  /// Returns a parser for the right shift operator, e.g., `>>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shr`](crate::lexer::OperatorToken::is_shr).
  shr,
  /// Returns a parser for the left shift assign operator, e.g., `<<=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shl_assign`](crate::lexer::OperatorToken::is_shl_assign).
  shl_assign,
  /// Returns a parser for the right shift assign operator, e.g., `>>=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shr_assign`](crate::lexer::OperatorToken::is_shr_assign).
  shr_assign,
  /// Returns a parser for the arrow operator, e.g., `->`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_arrow`](crate::lexer::OperatorToken::is_arrow).
  arrow,
  /// Returns a parser for the fat arrow operator, e.g., `=>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_fat_arrow`](crate::lexer::OperatorToken::is_fat_arrow).
  fat_arrow,
  /// Returns a parser for the pipe forward operator, e.g., `|>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_pipe_forward`](crate::lexer::OperatorToken::is_pipe_forward).
  pipe_forward,
  /// Returns a parser for the double colon operator, e.g., `::`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_double_colon`](crate::lexer::OperatorToken::is_double_colon).
  double_colon,
  /// Returns a parser for the backslash assign operator, e.g., `\=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_backslash_assign`](crate::lexer::OperatorToken::is_backslash_assign).
  backslash_assign,
});

/// Returns a parser for the modulo operator, e.g., `%`.
///
/// Depends on how `T` implements [`OperatorToken::is_mod`](crate::lexer::OperatorToken::is_mod).
pub fn modulo<'a, 'e: 'a, I, T, K, Error, E>(
  expected: impl ::core::ops::Fn() -> K + ::core::clone::Clone + 'a,
) -> impl crate::__private::chumsky::Parser<'a, I, crate::__private::utils::Spanned<T>, E>
+ ::core::clone::Clone
where
  I: crate::__private::LogoStream<'a, T>,
  T: crate::__private::OperatorToken<'a>,
  K: 'e,
  Error: ::core::convert::From<<T::Logos as crate::__private::logos::Logos<'a>>::Error>
    + ::core::convert::From<crate::__private::error::UnexpectedEot>
    + ::core::convert::From<crate::__private::error::UnexpectedToken<'a, T, K>>
    + 'a,
  E: crate::__private::chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
{
  crate::__private::chumsky::token::expected_token(
    <T as crate::__private::OperatorToken<'a>>::is_mod,
    move || crate::__private::utils::Expected::One(expected()),
  )
}
