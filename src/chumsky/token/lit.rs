super::macros::builtin_expected_token_parser!(LitToken {
  /// Returns a parser for any literal token.
  ///
  /// Depends on how `T` implements [`LitToken::is_literal`](LitToken::is_literal).
  literal,
  /// Returns a parser for numeric literals (integer/float/hex-float).
  ///
  /// Depends on how `T` implements [`LitToken::is_numeric_literal`](LitToken::is_numeric_literal).
  numeric_literal,
  /// Returns a parser for integer literals (includes decimal/hex/octal/binary).
  ///
  /// Depends on how `T` implements [`LitToken::is_integer_literal`](LitToken::is_integer_literal).
  integer_literal,
  /// Returns a parser for floating-point literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_float_literal`](LitToken::is_float_literal).
  float_literal,
  /// Returns a parser for decimal integer literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_decimal_literal`](LitToken::is_decimal_literal).
  decimal_literal,
  /// Returns a parser for hexadecimal integer literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_hexadecimal_literal`](LitToken::is_hexadecimal_literal).
  hexadecimal_literal,
  /// Returns a parser for octal integer literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_octal_literal`](LitToken::is_octal_literal).
  octal_literal,
  /// Returns a parser for binary integer literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_binary_literal`](LitToken::is_binary_literal).
  binary_literal,
  /// Returns a parser for hexadecimal floating-point literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_hex_float_literal`](LitToken::is_hex_float_literal).
  hex_float_literal,
  /// Returns a parser for any string literal.
  ///
  /// Depends on how `T` implements [`LitToken::is_string_literal`](LitToken::is_string_literal).
  string_literal,
  /// Returns a parser for inline string literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_inline_string_literal`](LitToken::is_inline_string_literal).
  inline_string_literal,
  /// Returns a parser for multiline string literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_multiline_string_literal`](LitToken::is_multiline_string_literal).
  multiline_string_literal,
  /// Returns a parser for raw string literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_raw_string_literal`](LitToken::is_raw_string_literal).
  raw_string_literal,
  /// Returns a parser for character literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_char_literal`](LitToken::is_char_literal).
  char_literal,
  /// Returns a parser for byte literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_byte_literal`](LitToken::is_byte_literal).
  byte_literal,
  /// Returns a parser for byte-string literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_byte_string_literal`](LitToken::is_byte_string_literal).
  byte_string_literal,
  /// Returns a parser for boolean literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_boolean_literal`](LitToken::is_boolean_literal).
  boolean_literal,
  /// Returns a parser for the `true` literal.
  ///
  /// Depends on how `T` implements [`LitToken::is_true_literal`](LitToken::is_true_literal).
  true_literal,
  /// Returns a parser for the `false` literal.
  ///
  /// Depends on how `T` implements [`LitToken::is_false_literal`](LitToken::is_false_literal).
  false_literal,
  /// Returns a parser for null/nil literals.
  ///
  /// Depends on how `T` implements [`LitToken::is_null_literal`](LitToken::is_null_literal).
  null_literal,
});
