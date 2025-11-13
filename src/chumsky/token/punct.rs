super::macros::builtin_expected_token_parser!(PunctuatorToken {
  /// Returns a parser for the dot punctuator, e.g., `.`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_dot`](PunctuatorToken::is_dot).
  dot,
  /// Returns a parser for the comma punctuator, e.g., `,`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_comma`](PunctuatorToken::is_comma).
  comma,
  /// Returns a parser for the colon punctuator, e.g., `:`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_colon`](PunctuatorToken::is_colon).
  colon,
  /// Returns a parser for the semicolon punctuator, e.g., `;`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_semicolon`](PunctuatorToken::is_semicolon).
  semicolon,
  /// Returns a parser for the exclamation punctuator, e.g., `!`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_exclamation`](PunctuatorToken::is_exclamation).
  exclamation,
  /// Returns a parser for the double-quote punctuator, e.g., `"`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_double_quote`](PunctuatorToken::is_double_quote).
  double_quote,
  /// Returns a parser for the apostrophe punctuator, e.g., `'`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_apostrophe`](PunctuatorToken::is_apostrophe).
  apostrophe,
  /// Returns a parser for the hash punctuator, e.g., `#`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_hash`](PunctuatorToken::is_hash).
  hash,
  /// Returns a parser for the dollar punctuator, e.g., `$`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_dollar`](PunctuatorToken::is_dollar).
  dollar,
  /// Returns a parser for the percent punctuator, e.g., `%`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_percent`](PunctuatorToken::is_percent).
  percent,
  /// Returns a parser for the ampersand punctuator, e.g., `&`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_ampersand`](PunctuatorToken::is_ampersand).
  ampersand,
  /// Returns a parser for the asterisk punctuator, e.g., `*`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_asterisk`](PunctuatorToken::is_asterisk).
  asterisk,
  /// Returns a parser for the plus punctuator, e.g., `+`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_plus`](PunctuatorToken::is_plus).
  plus,
  /// Returns a parser for the minus punctuator, e.g., `-`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_minus`](PunctuatorToken::is_minus).
  minus,
  /// Returns a parser for the slash punctuator, e.g., `/`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_slash`](PunctuatorToken::is_slash).
  slash,
  /// Returns a parser for the backslash punctuator, e.g., `\\`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_backslash`](PunctuatorToken::is_backslash).
  backslash,
  /// Returns a parser for the less-than punctuator, e.g., `<`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_angle_open`](PunctuatorToken::is_angle_open).
  angle_open,
  /// Returns a parser for the equals punctuator, e.g., `=`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_equal`](PunctuatorToken::is_equal).
  equal,
  /// Returns a parser for the greater-than punctuator, e.g., `>`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_angle_close`](PunctuatorToken::is_angle_close).
  angle_close,
  /// Returns a parser for the question punctuator, e.g., `?`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_question`](PunctuatorToken::is_question).
  question,
  /// Returns a parser for the at-sign punctuator, e.g., `@`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_at`](PunctuatorToken::is_at).
  at,
  /// Returns a parser for the left bracket punctuator, e.g., `[`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_bracket_open`](PunctuatorToken::is_bracket_open).
  bracket_open,
  /// Returns a parser for the right bracket punctuator, e.g., `]`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_bracket_close`](PunctuatorToken::is_bracket_close).
  bracket_close,
  /// Returns a parser for the left brace punctuator, e.g., `{`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_brace_open`](PunctuatorToken::is_brace_open).
  brace_open,
  /// Returns a parser for the right brace punctuator, e.g., `}`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_brace_close`](PunctuatorToken::is_brace_close).
  brace_close,
  /// Returns a parser for the left parenthesis punctuator, e.g., `(`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_paren_open`](PunctuatorToken::is_paren_open).
  paren_open,
  /// Returns a parser for the right parenthesis punctuator, e.g., `)`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_paren_close`](PunctuatorToken::is_paren_close).
  paren_close,
  /// Returns a parser for the backtick punctuator, e.g., `` ` ``.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_backtick`](PunctuatorToken::is_backtick).
  backtick,
  /// Returns a parser for the pipe punctuator, e.g., `|`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_pipe`](PunctuatorToken::is_pipe).
  pipe,
  /// Returns a parser for the caret punctuator, e.g., `^`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_caret`](PunctuatorToken::is_caret).
  caret,
  /// Returns a parser for the underscore punctuator, e.g., `_`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_underscore`](PunctuatorToken::is_underscore).
  underscore,
  /// Returns a parser for the tilde punctuator, e.g., `~`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_tilde`](PunctuatorToken::is_tilde).
  tilde,
});
