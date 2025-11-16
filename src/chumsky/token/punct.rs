super::macros::builtin_expected_token_parser!(PunctuatorToken {
  /// Returns a parser for the dot punctuator, e.g., `.`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_dot`](crate::lexer::PunctuatorToken::is_dot).
  dot,
  /// Returns a parser for the comma punctuator, e.g., `,`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_comma`](crate::lexer::PunctuatorToken::is_comma).
  comma,
  /// Returns a parser for the colon punctuator, e.g., `:`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_colon`](crate::lexer::PunctuatorToken::is_colon).
  colon,
  /// Returns a parser for the semicolon punctuator, e.g., `;`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_semicolon`](crate::lexer::PunctuatorToken::is_semicolon).
  semicolon,
  /// Returns a parser for the exclamation punctuator, e.g., `!`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_exclamation`](crate::lexer::PunctuatorToken::is_exclamation).
  exclamation,
  /// Returns a parser for the double-quote punctuator, e.g., `"`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_double_quote`](crate::lexer::PunctuatorToken::is_double_quote).
  double_quote,
  /// Returns a parser for the apostrophe punctuator, e.g., `'`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_apostrophe`](crate::lexer::PunctuatorToken::is_apostrophe).
  apostrophe,
  /// Returns a parser for the hash punctuator, e.g., `#`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_hash`](crate::lexer::PunctuatorToken::is_hash).
  hash,
  /// Returns a parser for the dollar punctuator, e.g., `$`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_dollar`](crate::lexer::PunctuatorToken::is_dollar).
  dollar,
  /// Returns a parser for the percent punctuator, e.g., `%`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_percent`](crate::lexer::PunctuatorToken::is_percent).
  percent,
  /// Returns a parser for the ampersand punctuator, e.g., `&`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_ampersand`](crate::lexer::PunctuatorToken::is_ampersand).
  ampersand,
  /// Returns a parser for the asterisk punctuator, e.g., `*`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_asterisk`](crate::lexer::PunctuatorToken::is_asterisk).
  asterisk,
  /// Returns a parser for the plus punctuator, e.g., `+`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_plus`](crate::lexer::PunctuatorToken::is_plus).
  plus,
  /// Returns a parser for the minus punctuator, e.g., `-`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_minus`](crate::lexer::PunctuatorToken::is_minus).
  minus,
  /// Returns a parser for the slash punctuator, e.g., `/`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_slash`](crate::lexer::PunctuatorToken::is_slash).
  slash,
  /// Returns a parser for the backslash punctuator, e.g., `\\`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_backslash`](crate::lexer::PunctuatorToken::is_backslash).
  backslash,
  /// Returns a parser for the less-than punctuator, e.g., `<`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_angle_open`](crate::lexer::PunctuatorToken::is_angle_open).
  angle_open,
  /// Returns a parser for the equals punctuator, e.g., `=`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_equal`](crate::lexer::PunctuatorToken::is_equal).
  equal,
  /// Returns a parser for the greater-than punctuator, e.g., `>`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_angle_close`](crate::lexer::PunctuatorToken::is_angle_close).
  angle_close,
  /// Returns a parser for the question punctuator, e.g., `?`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_question`](crate::lexer::PunctuatorToken::is_question).
  question,
  /// Returns a parser for the at-sign punctuator, e.g., `@`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_at`](crate::lexer::PunctuatorToken::is_at).
  at,
  /// Returns a parser for the left bracket punctuator, e.g., `[`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_bracket_open`](crate::lexer::PunctuatorToken::is_bracket_open).
  bracket_open,
  /// Returns a parser for the right bracket punctuator, e.g., `]`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_bracket_close`](crate::lexer::PunctuatorToken::is_bracket_close).
  bracket_close,
  /// Returns a parser for the left brace punctuator, e.g., `{`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_brace_open`](crate::lexer::PunctuatorToken::is_brace_open).
  brace_open,
  /// Returns a parser for the right brace punctuator, e.g., `}`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_brace_close`](crate::lexer::PunctuatorToken::is_brace_close).
  brace_close,
  /// Returns a parser for the left parenthesis punctuator, e.g., `(`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_paren_open`](crate::lexer::PunctuatorToken::is_paren_open).
  paren_open,
  /// Returns a parser for the right parenthesis punctuator, e.g., `)`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_paren_close`](crate::lexer::PunctuatorToken::is_paren_close).
  paren_close,
  /// Returns a parser for the backtick punctuator, e.g., `` ` ``.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_backtick`](crate::lexer::PunctuatorToken::is_backtick).
  backtick,
  /// Returns a parser for the pipe punctuator, e.g., `|`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_pipe`](crate::lexer::PunctuatorToken::is_pipe).
  pipe,
  /// Returns a parser for the caret punctuator, e.g., `^`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_caret`](crate::lexer::PunctuatorToken::is_caret).
  caret,
  /// Returns a parser for the underscore punctuator, e.g., `_`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_underscore`](crate::lexer::PunctuatorToken::is_underscore).
  underscore,
  /// Returns a parser for the tilde punctuator, e.g., `~`.
  ///
  /// Depends on how `T` implements [`PunctuatorToken::is_tilde`](crate::lexer::PunctuatorToken::is_tilde).
  tilde,
});
