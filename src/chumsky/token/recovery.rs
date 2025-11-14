use logos::Logos;

use crate::{
  DelimiterToken, Lexed, LogoStream, Token,
  chumsky::{Parser, extra::ParserExtra, prelude::*},
  utils::delimiter::Delimiter,
};

/// Emits a parser error without consuming input.
///
/// # Overview
///
/// `emit` is a tiny parser combinator that **records** an error by calling
/// [`Emitter::emit`](chumsky::extra::ParserExtra::Emitter) and then rewinds so the
/// surrounding parser can decide how to continue. No tokens are consumed, which makes
/// it perfect for recovery strategies where you need to log a diagnostic but keep the
/// lookahead intact.
///
/// # When to Use
///
/// - Inside `recover_with` to report why recovery was triggered.
/// - Alongside `skip_*` helpers to emit one diagnostic per skipped token.
/// - Any time you need to attach context-specific errors without advancing the stream.
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::emit;
///
/// parser.recover_with(chumsky::Parser::recover_with(
///     emit(MyError::MissingCloseBrace)
/// ).or(my_fallback_parser));
/// ```
///
/// The example above emits `MissingCloseBrace` but leaves the cursor untouched so
/// `my_fallback_parser` (or later combinators) can keep inspecting the same input.
pub fn emit<'a, I, T, Error, E>(err: Error) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: Clone + 'a,
{
  any()
    .validate(move |_, _, emitter| {
      emitter.emit(err.clone());
    })
    .rewind()
}

/// Scans ahead for a matching closing delimiter and rewinds before returning.
///
/// This function performs a non-destructive lookahead to check if a matching closing
/// delimiter exists in the token stream. It tracks nesting depth to find the correct
/// matching delimiter. After scanning, it always rewinds to the original position.
///
/// # Returns
///
/// - `Ok(true)` if a matching closing delimiter was found
/// - `Ok(false)` if EOF was reached without finding a match
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters:
///
/// ```text
/// {        // depth: 0 → 1
///   {      // depth: 1 → 2
///     }    // depth: 2 → 1 (nested close)
///   }      // depth: 1 → 0 (nested close)
/// }        // depth: 0 (FOUND - this matches!)
/// ```
///
/// # Use Cases
///
/// - Check if a block/expression is well-formed before parsing
/// - Decide recovery strategy based on delimiter presence
/// - Validate structure without consuming tokens
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::scan_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// // Check if there's a matching closing brace
/// if scan_closing_delimiter(Delimiter::Brace).parse(stream) {
///     // Safe to parse the block
///     parse_block(stream)
/// } else {
///     // No closing brace found - use recovery
///     recover_block(stream)
/// }
/// ```
///
/// # See Also
///
/// - [`skip_to_closing_delimiter`]: Skip to delimiter (for recovery)
/// - [`skip_through_closing_delimiter`]: Skip through delimiter (for recovery)
pub fn scan_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, bool, E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let checkpoint = inp.save();
    let mut depth = 0;
    loop {
      match inp.peek() {
        Some(Lexed::Token(tok)) if delimiter.is_open(&*tok) => {
          depth += 1;
          inp.skip();
        }
        Some(Lexed::Token(tok)) if delimiter.is_close(&*tok) => {
          if depth == 0 {
            inp.rewind(checkpoint);
            return Ok(true);
          } else {
            depth -= 1;
            inp.skip();
          }
        }
        None => {
          inp.rewind(checkpoint);
          return Ok(false);
        }
        _ => {
          inp.skip();
        }
      }
    }
  })
}

/// Skips tokens until reaching a matching closing delimiter.
///
/// This function consumes tokens until it finds a closing delimiter that matches
/// the given delimiter type at depth 0. It tracks nesting depth to find the correct
/// matching delimiter. The input is left positioned **BEFORE** the closing delimiter
/// (the delimiter itself is not consumed).
///
/// # Returns
///
/// - `Ok(Some(n))` where `n` is the number of tokens skipped if delimiter found
/// - `Ok(None)` if EOF was reached without finding a match
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters:
///
/// ```text
/// {        // Skip this (depth 0 → 1)
///   {      // Skip this (depth 1 → 2)
///     }    // Skip this (depth 2 → 1)
///   }      // Skip this (depth 1 → 0)
/// }        // STOP HERE (depth 0, positioned BEFORE this})
/// ```
///
/// # Error Handling
///
/// Lexer errors encountered during skipping are emitted but do not stop the scan.
/// This ensures comprehensive error reporting even during recovery.
///
/// # Use Cases
///
/// - **Error recovery**: Skip malformed content until finding delimiter
/// - **Block recovery**: Skip to end of block when parsing fails
/// - **Synchronization**: Find recovery point at known delimiter
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::skip_to_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// // Skip malformed block content
/// match skip_to_closing_delimiter(Delimiter::Brace).parse(stream) {
///     Ok(Some(n)) => {
///         println!("Skipped {} tokens", n);
///         // Now positioned at closing brace, can consume it
///         consume_closing_brace(stream);
///     }
///     Ok(None) => {
///         // Reached EOF without finding closing brace
///         emit_unclosed_error();
///     }
/// }
/// ```
///
/// # See Also
///
/// - [`scan_closing_delimiter`]: Check if delimiter exists (non-destructive)
/// - [`skip_through_closing_delimiter`]: Skip and consume delimiter
pub fn skip_to_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, Result<usize, usize>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let mut depth = 0;
    let mut skipped = 0;

    loop {
      match inp.peek() {
        Some(Lexed::Token(tok)) if delimiter.is_open(&*tok) => {
          depth += 1;
          inp.skip();
          skipped += 1;
        }
        Some(Lexed::Token(tok)) if delimiter.is_close(&*tok) => {
          if depth == 0 {
            // Found matching closing delimiter!
            // Leave positioned BEFORE it (don't consume)
            return Ok(Ok(skipped));
          } else {
            depth -= 1;
            inp.skip();
            skipped += 1;
          }
        }
        None => {
          inp.skip();
          // Reached EOF without finding closing delimiter
          return Ok(Err(skipped));
        }
        Some(Lexed::Error(_)) => {
          // Emit lexer error but continue recovery
          let _ = inp.parse(any().validate(|tok, _, emitter| {
            // we know this is an error token
            if let Lexed::Error(e) = tok {
              emitter.emit(<Error as From<_>>::from(e));
            }
          }));
          skipped += 1;
        }
        _ => {
          inp.skip();
          skipped += 1;
        }
      }
    }
  })
}

/// Skips tokens until reaching and consuming a matching closing delimiter.
///
/// This function consumes tokens until it finds a closing delimiter that matches
/// the given delimiter type at depth 0, then consumes the closing delimiter as well.
/// It tracks nesting depth to find the correct matching delimiter. The input is left
/// positioned **AFTER** the closing delimiter.
///
/// # Returns
///
/// - `Ok(true)` if delimiter was found and consumed
/// - `Ok(false)` if EOF was reached without finding a match
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters:
///
/// ```text
/// {        // Skip this (depth 0 → 1)
///   {      // Skip this (depth 1 → 2)
///     }    // Skip this (depth 2 → 1)
///   }      // Skip this (depth 1 → 0)
/// }        // CONSUME THIS (depth 0) → positioned AFTER }
/// ```
///
/// # Error Handling
///
/// Lexer errors encountered during skipping are emitted but do not stop the scan.
/// This ensures comprehensive error reporting even during recovery.
///
/// # Use Cases
///
/// - **Skip malformed blocks**: Discard entire unparseable block
/// - **Fast-forward recovery**: Skip to next valid parse point
/// - **Nested block cleanup**: Skip failed nested structures
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::skip_through_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// // Completely skip a malformed nested block
/// match statement_parser.parse(stream) {
///     Ok(stmt) => statements.push(stmt),
///     Err(_) => {
///         // Failed to parse - skip the entire malformed block
///         if skip_through_closing_delimiter(Delimiter::Brace).parse(stream) {
///             // Successfully skipped, continue with next statement
///         } else {
///             // Reached EOF - block was unclosed
///             break;
///         }
///     }
/// }
/// ```
///
/// # Comparison with skip_to_closing_delimiter
///
/// ```text
/// skip_to_closing_delimiter:
///   { content } more
///            ^ positioned here (before })
///
/// skip_through_closing_delimiter:
///   { content } more
///              ^ positioned here (after })
/// ```
///
/// Use `skip_to` when you want to manually handle the closing delimiter
/// (e.g., to emit custom errors or track positions).
///
/// Use `skip_through` when you want to completely discard the block including
/// its delimiter (e.g., when recovering from malformed nested blocks).
///
/// # See Also
///
/// - [`scan_closing_delimiter`]: Check if delimiter exists (non-destructive)
/// - [`skip_to_closing_delimiter`]: Skip to delimiter (leaves delimiter)
pub fn skip_through_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, bool, E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let mut depth = 0;

    loop {
      match inp.peek() {
        Some(Lexed::Token(tok)) if delimiter.is_open(&*tok) => {
          depth += 1;
          inp.skip();
        }
        Some(Lexed::Token(tok)) if delimiter.is_close(&*tok) => {
          if depth == 0 {
            // Found matching closing delimiter!
            // Consume it and position AFTER it
            inp.skip();
            return Ok(true);
          } else {
            depth -= 1;
            inp.skip();
          }
        }
        None => {
          // Reached EOF without finding closing delimiter
          return Ok(false);
        }
        Some(Lexed::Error(_)) => {
          // Emit lexer error but continue recovery
          let _ = inp.parse(any().validate(|tok, _, emitter| {
            // we know this is an error token
            if let Lexed::Error(e) = tok {
              emitter.emit(<Error as From<_>>::from(e));
            }
          }));
        }
        _ => {
          inp.skip();
        }
      }
    }
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    Lexed, Token, Tokenizer,
    chumsky::{error::Cheap, extra, prelude::any},
    utils::{Span, Spanned, delimiter::Delimiter},
  };
  use logos::Logos;

  // Custom error type for testing - newtype wrapper so we can impl From<()>
  #[derive(Debug, Clone, PartialEq)]
  struct TestError(Cheap<Span>);

  impl<'a, I, L> chumsky::error::LabelError<'a, I, L> for TestError
  where
    I: LogoStream<'a, TestToken>,
  {
    fn expected_found<E>(
      _expected: E,
      _found: Option<chumsky::util::Maybe<I::Token, &'a I::Token>>,
      span: I::Span,
    ) -> Self
    where
      E: IntoIterator<Item = L>,
    {
      TestError(Cheap::new(span))
    }
  }

  impl<'a, I> chumsky::error::Error<'a, I> for TestError where I: LogoStream<'a, TestToken> {}

  impl From<()> for TestError {
    fn from(_: ()) -> Self {
      TestError(Cheap::new(Span::new(0, 0)))
    }
  }

  // Test token type with delimiters
  #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
  #[logos(skip r"[ \t\n\f]+")]
  enum TestTokens {
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[regex(r"[a-z]+")]
    Word,
    #[regex(r"[0-9]+")]
    Number,
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  enum TestTokenKind {
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Word,
    Number,
  }

  #[derive(Debug, Clone, PartialEq)]
  struct TestToken {
    kind: TestTokenKind,
    logos: TestTokens,
  }

  impl Token<'_> for TestToken {
    type Char = char;
    type Kind = TestTokenKind;
    type Logos = TestTokens;

    fn kind(&self) -> Self::Kind {
      self.kind
    }
  }

  impl From<TestTokens> for TestToken {
    fn from(logos: TestTokens) -> Self {
      let kind = match logos {
        TestTokens::LParen => TestTokenKind::LParen,
        TestTokens::RParen => TestTokenKind::RParen,
        TestTokens::LBrace => TestTokenKind::LBrace,
        TestTokens::RBrace => TestTokenKind::RBrace,
        TestTokens::LBracket => TestTokenKind::LBracket,
        TestTokens::RBracket => TestTokenKind::RBracket,
        TestTokens::Word => TestTokenKind::Word,
        TestTokens::Number => TestTokenKind::Number,
      };
      TestToken { kind, logos }
    }
  }

  impl crate::DelimiterToken<'_> for TestToken {
    fn is_paren_open(&self) -> bool {
      matches!(self.kind, TestTokenKind::LParen)
    }

    fn is_paren_close(&self) -> bool {
      matches!(self.kind, TestTokenKind::RParen)
    }

    fn is_brace_open(&self) -> bool {
      matches!(self.kind, TestTokenKind::LBrace)
    }

    fn is_brace_close(&self) -> bool {
      matches!(self.kind, TestTokenKind::RBrace)
    }

    fn is_bracket_open(&self) -> bool {
      matches!(self.kind, TestTokenKind::LBracket)
    }

    fn is_bracket_close(&self) -> bool {
      matches!(self.kind, TestTokenKind::RBracket)
    }
  }

  type TestTokenizer<'a> = Tokenizer<'a, TestToken>;

  mod scan_closing_delimiter_tests {
    use super::*;

    #[test]
    fn test_simple_matching_brace() {
      let input = "word }";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_simple_matching_paren() {
      let input = "42 )";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Paren)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_simple_matching_bracket() {
      let input = "foo ]";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Bracket)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_nested_braces() {
      let input = "{ { } } }";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_nested_parens() {
      let input = "( ( ) ( ) ) )";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Paren)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_eof_without_closing() {
      let input = "word { word";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(false));
    }

    #[test]
    fn test_eof_immediately() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(false));
    }

    #[test]
    fn test_wrong_delimiter_type() {
      let input = "word )";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      // Should not find brace, only paren exists
      assert_eq!(result.into_result(), Ok(false));
    }

    #[test]
    fn test_non_destructive() {
      let input = "foo bar }";
      let stream = TestTokenizer::new(input);

      // First scan
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream.clone());
      assert_eq!(result.into_result(), Ok(true));

      // Second scan should still work (non-destructive)
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }
  }

  mod skip_to_closing_delimiter_tests {
    use super::*;

    #[test]
    fn test_simple_skip() {
      let input = "word }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok((Ok(1), TestTokenKind::RBrace))); // Skipped 1 token (word)
    }

    #[test]
    fn test_skip_multiple_tokens() {
      let input = "foo bar 42 }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok((Ok(3), TestTokenKind::RBrace))); // Skipped 3 tokens
    }

    #[test]
    fn test_skip_nested() {
      let input = "foo { bar } baz }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      // Should skip: foo, {, bar, }, baz = 5 tokens
      assert_eq!(result.into_result(), Ok((Ok(5), TestTokenKind::RBrace)));
    }

    #[test]
    fn test_skip_deeply_nested() {
      let input = "{ { { } } } }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      // Should skip: {, {, {, }, }, } = 6 tokens
      assert_eq!(result.into_result(), Ok((Ok(6), TestTokenKind::RBrace)));
    }

    #[test]
    fn test_skip_eof() {
      let input = "foo bar";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(Err(2)));
    }

    #[test]
    fn test_skip_immediate_match() {
      let input = "}";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok((Ok(0), TestTokenKind::RBrace))); // No tokens skipped
    }

    #[test]
    fn test_skip_empty_input() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(Err(0)));
    }

    #[test]
    fn test_position_after_skip() {
      let input = "foo } bar";
      let stream = TestTokenizer::new(input);

      // Skip to closing brace
      let parser = skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
        .then(any()) // Should consume the }
        .then(any()); // Should consume bar

      let result = parser.parse(stream);
      assert!(result.into_result().is_ok());
    }
  }

  mod skip_through_closing_delimiter_tests {
    use super::*;

    #[test]
    fn test_simple_skip_through() {
      let input = "word }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_skip_through_nested() {
      let input = "foo { bar } baz }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_skip_through_deeply_nested() {
      let input = "{ { { } } } }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_skip_through_eof() {
      let input = "foo bar";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(false));
    }

    #[test]
    fn test_skip_through_immediate_match() {
      let input = "}";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(true));
    }

    #[test]
    fn test_skip_through_empty_input() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(false));
    }

    #[test]
    fn test_position_after_skip_through() {
      let input = "foo } bar";
      let stream = TestTokenizer::new(input);

      // Skip through closing brace
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then(any()); // Should consume bar (positioned after })

      let result = parser.parse(stream);
      assert!(result.into_result().is_ok());
      // The any() should successfully parse "bar" since we're after }
    }

    #[test]
    fn test_skip_through_vs_skip_to_difference() {
      // Test that skip_through consumes the delimiter but skip_to doesn't

      // skip_to: should leave } unconsumed
      let input1 = "word }";
      let stream1 = TestTokenizer::new(input1);
      let parser1 = skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(
        Delimiter::Brace,
      )
      .then(any().filter(|tok: &Lexed<'_, TestToken>| {
        matches!(
          tok,
          Lexed::Token(Spanned {
            data: TestToken {
              kind: TestTokenKind::RBrace,
              ..
            },
            ..
          })
        )
      }));
      let result1 = parser1.parse(stream1);
      assert!(
        result1.into_result().is_ok(),
        "skip_to should leave }} to be consumed"
      );

      // skip_through: should consume }, next token should be something else
      let input2 = "word } bar";
      let stream2 = TestTokenizer::new(input2);
      let parser2 =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then(any().filter(|tok: &Lexed<'_, TestToken>| {
            matches!(
              tok,
              Lexed::Token(Spanned {
                data: TestToken {
                  kind: TestTokenKind::Word,
                  ..
                },
                ..
              })
            )
          }));
      let result2 = parser2.parse(stream2);
      assert!(
        result2.into_result().is_ok(),
        "skip_through should consume }}, next should be bar"
      );
    }
  }

  mod mixed_delimiter_tests {
    use super::*;

    #[test]
    fn test_mixed_delimiters_brace_in_paren() {
      let input = "{ } )";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Paren).then(
          any().try_map(|tok: Lexed<'_, TestToken>, span: Span| match tok {
            Lexed::Token(Spanned { data: tok, .. }) => Ok(tok.kind),
            Lexed::Error(_) => Err(TestError(Cheap::new(span))),
          }),
        );
      let result = parser.parse(stream);
      // Should skip: (, {, } = 3 tokens, stop before )
      assert_eq!(result.into_result(), Ok((Ok(2), TestTokenKind::RParen)));
    }

    #[test]
    fn test_mixed_delimiters_paren_in_brace() {
      let input = "{ ( ) }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      // Should skip: {, (, ) = 3 tokens, stop before }
      assert_eq!(result.into_result(), Ok(Err(4)));
    }

    #[test]
    fn test_complex_nesting() {
      let input = "[ { ( ) } ( { } ) ]";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Bracket);
      let result = parser.parse(stream);
      // Should skip: [, {, (, ), }, (, {, }, ) = 9 tokens
      assert_eq!(result.into_result(), Ok(Err(10)));
    }

    #[test]
    fn test_scan_ignores_wrong_delimiter_type() {
      let input = "( ) }";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      // Should find the } after skipping ()
      assert_eq!(result.into_result(), Ok(true));
    }
  }
}
