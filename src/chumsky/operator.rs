super::macros::builtin_expected_token_parser!(OperatorToken {
  /// Returns a parser for the colon assign operator, e.g., `:=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_colon_eq_assign`](OperatorToken::is_colon_eq_assign).
  colon_eq_assign,
  /// Returns a parser for the logical XOR operator, e.g., `^^`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_xor`](OperatorToken::is_logical_xor).
  logical_xor,
  /// Returns a parser for the logical AND operator, e.g., `&&`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_and`](OperatorToken::is_logical_and).
  logical_and,
  /// Returns a parser for the logical OR operator, e.g., `||`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_or`](OperatorToken::is_logical_or).
  logical_or,
  /// Returns a parser for the logical NOT operator, e.g., `!`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_logical_not`](OperatorToken::is_logical_not).
  logical_not,
  /// Returns a parser for the equal operator, e.g., `==`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_eq`](OperatorToken::is_eq).
  eq,
  /// Returns a parser for the not equal operator, e.g., `!=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_ne`](OperatorToken::is_ne).
  ne,
  /// Returns a parser for the strict equal operator, e.g., `===`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_eq`](OperatorToken::is_strict_eq).
  strict_eq,
  /// Returns a parser for the strict not equal operator, e.g., `!==`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_strict_ne`](OperatorToken::is_strict_ne).
  strict_ne,
  /// Returns a parser for the less than operator, e.g., `<`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_lt`](OperatorToken::is_lt).
  lt,
  /// Returns a parser for the less than or equal to operator, e.g., `<=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_le`](OperatorToken::is_le).
  le,
  /// Returns a parser for the greater than operator, e.g., `>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_gt`](OperatorToken::is_gt).
  gt,
  /// Returns a parser for the greater than or equal to operator, e.g., `>=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_ge`](OperatorToken::is_ge).
  ge,
  /// Returns a parser for the left shift operator, e.g., `<<`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shl`](OperatorToken::is_shl).
  shl,
  /// Returns a parser for the right shift operator, e.g., `>>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shr`](OperatorToken::is_shr).
  shr,
  /// Returns a parser for the left shift assign operator, e.g., `<<=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shl_assign`](OperatorToken::is_shl_assign).
  shl_assign,
  /// Returns a parser for the right shift assign operator, e.g., `>>=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_shr_assign`](OperatorToken::is_shr_assign).
  shr_assign,
  /// Returns a parser for the arrow operator, e.g., `->`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_arrow`](OperatorToken::is_arrow).
  arrow,
  /// Returns a parser for the fat arrow operator, e.g., `=>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_fat_arrow`](OperatorToken::is_fat_arrow).
  fat_arrow,
  /// Returns a parser for the pipe forward operator, e.g., `|>`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_pipe_forward`](OperatorToken::is_pipe_forward).
  pipe_forward,
  /// Returns a parser for the double colon operator, e.g., `::`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_double_colon`](OperatorToken::is_double_colon).
  double_colon,
  /// Returns a parser for the backslash assign operator, e.g., `\=`.
  ///
  /// Depends on how `T` implements [`OperatorToken::is_backslash_assign`](OperatorToken::is_backslash_assign).
  backslash_assign,
});
