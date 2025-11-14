use logos::Logos;

use crate::{
  DelimiterToken, Lexed, LogoStream, Token,
  chumsky::{Parser, extra::ParserExtra, prelude::*},
  utils::{Span, Spanned, delimiter::Delimiter},
};

/// Emits a parser error without consuming input.
///
/// This parser combinator records an error by calling the error emitter, then rewinds
/// the input position so no tokens are consumed. This is essential for error recovery
/// strategies where you need to report diagnostics while allowing subsequent parsers
/// to inspect the same tokens.
///
/// # Parameters
///
/// - `err`: The error to emit. Must implement `Clone` since the parser may be called multiple times.
///
/// # Returns
///
/// A parser that:
/// - Always succeeds with `()`
/// - Emits the provided error via the parser's error emitter
/// - Leaves the input stream at its original position (non-destructive)
///
/// # Use Cases
///
/// - **Recovery contexts**: Report why recovery was triggered without consuming tokens
/// - **Error accumulation**: Emit diagnostic errors while continuing to parse
/// - **Lookahead validation**: Report issues found during lookahead without advancing
/// - **Custom error reporting**: Add context-specific errors at any parse point
///
/// # Examples
///
/// ## Basic Error Emission
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::emit;
///
/// // Emit an error when recovery is triggered
/// my_parser
///   .recover_with(via_parser(
///     emit(MyError::MissingCloseBrace)
///       .ignore_then(fallback_parser)
///   ))
/// ```
///
/// ## Conditional Error Emission
///
/// ```rust,ignore
/// // Emit error only if condition is met
/// scan_closing_delimiter(Delimiter::Brace)
///   .try_map(|(span, found), _| {
///     if found.is_none() {
///       emit(UnclosedBrace::new(span)).parse(stream);
///     }
///     Ok(found)
///   })
/// ```
///
/// ## Multiple Error Emissions
///
/// ```rust,ignore
/// // Report multiple issues without consuming input
/// emit(Warning::DeprecatedSyntax)
///   .ignore_then(emit(Warning::ConsiderRefactoring))
///   .ignore_then(actual_parser)
/// ```
///
/// # See Also
///
/// - [`emit_with`]: Lazy version that generates the error on-demand
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

/// Emits a parser error without consuming input (lazy version).
///
/// This is the lazy variant of [`emit`] that generates the error on-demand each time
/// the parser is invoked. Use this when error construction is expensive or when the
/// error needs to capture dynamic state at parse-time rather than parser-construction-time.
///
/// # Parameters
///
/// - `err`: A closure that produces the error. Called each time the parser executes.
///
/// # Returns
///
/// A parser that:
/// - Always succeeds with `()`
/// - Calls `err()` and emits the resulting error via the parser's error emitter
/// - Leaves the input stream at its original position (non-destructive)
///
/// # When to Use emit_with vs emit
///
/// Use `emit_with` when:
/// - Error construction captures parser state (spans, tokens, etc.)
/// - Error creation is computationally expensive
/// - You need different error instances for each invocation
///
/// Use [`emit`] when:
/// - The error is a simple constant or pre-constructed value
/// - Error construction has no side effects or captured state
///
/// # Examples
///
/// ## Capturing Parse State
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::emit_with;
///
/// // Error message includes dynamic span information
/// my_parser
///   .recover_with(via_parser(
///     emit_with(|| MyError::UnclosedDelimiter {
///       expected: "}",
///       span: current_span(), // Captured at parse-time
///     })
///     .ignore_then(fallback_parser)
///   ))
/// ```
///
/// ## Expensive Error Construction
///
/// ```rust,ignore
/// // Build detailed error with context only when needed
/// emit_with(|| {
///   let context = expensive_context_builder();
///   MyError::WithContext {
///     message: "Invalid syntax",
///     context,
///   }
/// })
/// ```
///
/// ## Dynamic Error Selection
///
/// ```rust,ignore
/// // Choose error type based on current parse state
/// emit_with(|| {
///   if in_strict_mode() {
///     MyError::StrictModeViolation
///   } else {
///     MyError::Warning
///   }
/// })
/// ```
///
/// # Performance Note
///
/// The closure is called every time the parser runs. If the error is a constant,
/// prefer [`emit`] which clones a pre-constructed error instead of calling a closure.
///
/// # See Also
///
/// - [`emit`]: Eager version that clones a pre-constructed error
pub fn emit_with<'a, I, T, Error, E>(
  err: impl Fn() -> Error + Clone + 'a,
) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: 'a,
{
  any()
    .validate(move |_, _, emitter| {
      emitter.emit(err());
    })
    .rewind()
}

/// Scans ahead for a matching closing delimiter and rewinds before returning.
///
/// This function performs a non-destructive lookahead to check if a matching closing
/// delimiter exists in the token stream. It tracks nesting depth to find the correct
/// matching delimiter. After scanning, it **always rewinds** to the original position,
/// leaving the input unchanged.
///
/// # Parameters
///
/// - `delimiter`: The delimiter type to search for (e.g., `Delimiter::Brace` for `{}`)
///
/// # Returns
///
/// Returns `(Span, Option<Spanned<T>>)` where:
/// - `Span`: The span from the current position to where the scan stopped (EOF or delimiter)
/// - `Option<Spanned<T>>`:
///   - `Some(token)`: Found a matching closing delimiter at depth 0, with its span and data
///   - `None`: Reached EOF without finding a matching delimiter
///
/// **Important**: The input stream is always rewound to its original position after scanning.
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters by tracking depth:
///
/// ```text
/// {        // depth: 0 → 1 (skip this opening)
///   {      // depth: 1 → 2 (skip this opening)
///     }    // depth: 2 → 1 (skip this closing, not at depth 0)
///   }      // depth: 1 → 0 (skip this closing, not at depth 0)
/// }        // depth: 0 (FOUND - this matches!)
/// ```
///
/// # Use Cases
///
/// - **Pre-validation**: Check if a block is well-formed before attempting to parse it
/// - **Recovery decisions**: Choose different recovery strategies based on delimiter presence
/// - **Diagnostic messages**: Include "expected closing delimiter" information with precise spans
/// - **Structure validation**: Verify nested structures without consuming tokens
///
/// # Examples
///
/// ## Basic Delimiter Check
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::scan_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// let (span, found) = scan_closing_delimiter(Delimiter::Brace).parse(stream)?;
///
/// match found {
///     Some(closing_token) => {
///         // Found closing brace - safe to parse the block
///         println!("Well-formed block ending at {:?}", closing_token.span);
///         parse_block(stream)
///     }
///     None => {
///         // No closing brace found - emit error and use recovery
///         emit(UnclosedBrace::new(span));
///         recover_block(stream)
///     }
/// }
/// ```
///
/// ## Choosing Recovery Strategy
///
/// ```rust,ignore
/// // Check if recovery is possible before attempting it
/// let (scan_span, maybe_close) = scan_closing_delimiter(Delimiter::Brace).parse(stream)?;
///
/// if maybe_close.is_some() {
///     // Delimiter exists - use skip-to recovery
///     skip_to_closing_delimiter(Delimiter::Brace).parse(stream)?;
///     // ... continue parsing after the brace
/// } else {
///     // No delimiter - use different recovery (e.g., synchronize on keywords)
///     skip_until_keyword().parse(stream)?;
/// }
/// ```
///
/// ## Preserving Token Information
///
/// ```rust,ignore
/// let (_, found) = scan_closing_delimiter(Delimiter::Paren).parse(stream)?;
///
/// if let Some(closing_paren) = found {
///     // Access the actual token for detailed diagnostics
///     println!("Closing paren at line {}, col {}",
///              closing_paren.span.start(),
///              closing_paren.span.end());
///
///     // Could check token properties if needed
///     // e.g., closing_paren.data.is_paren_close()
/// }
/// ```
///
/// # Performance Note
///
/// This function scans the entire token stream until finding the delimiter or EOF,
/// then rewinds. For large blocks with deep nesting, this may scan many tokens.
/// The scan is linear O(n) in the number of tokens between the current position
/// and the closing delimiter.
///
/// # See Also
///
/// - [`skip_to_closing_delimiter`]: Consumes tokens up to (but not including) the delimiter
/// - [`skip_through_closing_delimiter`]: Consumes tokens through (and including) the delimiter
pub fn scan_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, (Span, Option<Spanned<T>>), E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let checkpoint = inp.save();
    let before = inp.cursor();
    let mut depth = 0;
    loop {
      match inp.peek() {
        Some(Lexed::Token(tok)) if delimiter.is_open(&*tok) => {
          depth += 1;
          inp.skip();
        }
        Some(Lexed::Token(tok)) if delimiter.is_close(&*tok) => {
          if depth == 0 {
            let span = inp.span_since(&before);
            inp.rewind(checkpoint);
            return Ok((span, Some(tok)));
          } else {
            depth -= 1;
            inp.skip();
          }
        }
        None => {
          let span = inp.span_since(&before);
          inp.rewind(checkpoint);
          return Ok((span, None));
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
/// # Parameters
///
/// - `delimiter`: The delimiter type to search for (e.g., `Delimiter::Brace` for `{}`)
///
/// # Returns
///
/// Returns `Result<(usize, Span, Spanned<T>), (usize, Span)>` where:
///
/// - `Ok((count, span, token))`: Found and stopped before the closing delimiter
///   - `count`: Number of tokens skipped (not including the delimiter)
///   - `span`: Span from start position to just before the delimiter
///   - `token`: The closing delimiter token with its span and data
///
/// - `Err((count, span))`: Reached EOF without finding the delimiter
///   - `count`: Number of tokens consumed before reaching EOF
///   - `span`: Span from start position to EOF
///
/// **Important**: When successful (`Ok`), the input is positioned BEFORE the closing delimiter.
/// You can then consume it manually or inspect it before deciding how to proceed.
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters by tracking depth:
///
/// ```text
/// {        // Skip this (depth 0 → 1)
///   {      // Skip this (depth 1 → 2)
///     }    // Skip this (depth 2 → 1, nested close)
///   }      // Skip this (depth 1 → 0, nested close)
/// }        // STOP HERE (depth 0, positioned BEFORE this })
/// ```
///
/// # Error Handling
///
/// Lexer errors encountered during skipping are emitted via the error emitter but do
/// not stop the scan. This ensures comprehensive error reporting even during recovery,
/// allowing the parser to report both the skipped malformed tokens and the structural
/// delimiter mismatch.
///
/// # Use Cases
///
/// - **Malformed block recovery**: Skip unparseable content until finding the block's end
/// - **Error synchronization**: Find a known delimiter to resume parsing
/// - **Diagnostic spans**: Report exactly what content was skipped during recovery
/// - **Manual delimiter handling**: Inspect or validate the delimiter before consuming it
///
/// # Examples
///
/// ## Basic Recovery
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::skip_to_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// match skip_to_closing_delimiter(Delimiter::Brace).parse(stream)? {
///     Ok((count, span, closing_token)) => {
///         println!("Skipped {} malformed tokens spanning {:?}", count, span);
///         // Now positioned BEFORE the closing brace
///         // Consume it manually
///         let brace = any().parse(stream)?;
///         // Continue parsing after the block
///     }
///     Err((count, span)) => {
///         // Hit EOF without finding closing brace
///         emit(UnclosedBrace::new(span))?;
///         // Can't recover further
///     }
/// }
/// ```
///
/// ## Conditional Recovery
///
/// ```rust,ignore
/// // Try to skip to delimiter, but validate it before consuming
/// match skip_to_closing_delimiter(Delimiter::Paren).parse(stream)? {
///     Ok((skipped, span, closing)) => {
///         if skipped > MAX_RECOVERY_TOKENS {
///             // Skipped too much - might be in wrong context
///             return Err("Unable to recover: too many tokens skipped");
///         }
///         // Recovery looks reasonable, consume the delimiter
///         any().parse(stream)?;
///     }
///     Err(_) => {
///         // Use alternative recovery strategy
///         skip_until_keyword().parse(stream)?;
///     }
/// }
/// ```
///
/// ## Detailed Diagnostics
///
/// ```rust,ignore
/// match skip_to_closing_delimiter(Delimiter::Bracket).parse(stream)? {
///     Ok((count, span, closing_bracket)) => {
///         // Emit rich diagnostic with skipped content span
///         emit(Warning::MalformedArrayContent {
///             skipped_count: count,
///             malformed_span: span,
///             recovered_at: closing_bracket.span,
///         });
///         any().parse(stream)?; // Consume the ]
///     }
///     Err((count, span)) => {
///         emit(Error::UnclosedArray {
///             started_at: span.start(),
///             tokens_parsed: count,
///         });
///     }
/// }
/// ```
///
/// # Performance Note
///
/// This function consumes tokens linearly until finding the delimiter or EOF.
/// Time complexity is O(n) where n is the number of tokens until the delimiter.
///
/// # See Also
///
/// - [`scan_closing_delimiter`]: Non-destructive check without consuming tokens
/// - [`skip_through_closing_delimiter`]: Consumes the delimiter as well
#[allow(clippy::type_complexity)]
pub fn skip_to_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, Result<(usize, Span, Spanned<T>), (usize, Span)>, E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let mut depth = 0;
    let mut skipped = 0;
    let before = inp.cursor();

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
            return Ok(Ok((skipped, inp.span_since(&before), tok)));
          } else {
            depth -= 1;
            inp.skip();
            skipped += 1;
          }
        }
        None => {
          inp.skip();
          // Reached EOF without finding closing delimiter
          return Ok(Err((skipped, inp.span_since(&before))));
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
/// the given delimiter type at depth 0, then **also consumes the closing delimiter**.
/// It tracks nesting depth to find the correct matching delimiter. The input is left
/// positioned **AFTER** the closing delimiter.
///
/// # Parameters
///
/// - `delimiter`: The delimiter type to search for (e.g., `Delimiter::Brace` for `{}`)
///
/// # Returns
///
/// Returns `(Span, Option<Spanned<T>>)` where:
/// - `Span`: The span from start position through the closing delimiter (or to EOF)
/// - `Option<Spanned<T>>`:
///   - `Some(token)`: Found and consumed the closing delimiter
///   - `None`: Reached EOF without finding a matching delimiter
///
/// **Important**: When successful (`Some`), the input is positioned AFTER the closing delimiter.
/// The delimiter has been consumed and cannot be inspected after this call.
///
/// # Delimiter Matching
///
/// The function correctly handles nested delimiters by tracking depth:
///
/// ```text
/// {        // Skip this (depth 0 → 1)
///   {      // Skip this (depth 1 → 2)
///     }    // Skip this (depth 2 → 1, nested close)
///   }      // Skip this (depth 1 → 0, nested close)
/// }        // CONSUME THIS (depth 0) → positioned AFTER }
/// ```
///
/// # Error Handling
///
/// Lexer errors encountered during skipping are emitted via the error emitter but do
/// not stop the scan. This ensures comprehensive error reporting even during recovery,
/// allowing the parser to report all malformed tokens encountered while skipping.
///
/// # Use Cases
///
/// - **Complete block discard**: Skip entire unparseable block including its delimiters
/// - **Fast-forward recovery**: Quickly advance to next valid parse point
/// - **Nested structure cleanup**: Discard failed nested blocks entirely
/// - **Statement-level recovery**: Skip malformed statements in block parsing
///
/// # Examples
///
/// ## Statement-Level Recovery
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::skip_through_closing_delimiter;
/// use logosky::utils::delimiter::Delimiter;
///
/// // Parse multiple statements, recovering from failures
/// let statements = statement_parser
///     .recover_with(via_parser(
///         skip_through_closing_delimiter(Delimiter::Brace)
///             .try_map(|(span, found), _| {
///                 match found {
///                     Some(_) => Ok(ErrorNode::new(span)), // Recovered
///                     None => Err(UnclosedBlock::new(span)), // Can't recover
///                 }
///             })
///     ))
///     .repeated()
///     .collect();
/// ```
///
/// ## Block-Level Recovery Loop
///
/// ```rust,ignore
/// let mut blocks = vec![];
///
/// loop {
///     match block_parser.parse(stream) {
///         Ok(block) => blocks.push(block),
///         Err(_) => {
///             // Failed to parse - skip this malformed block entirely
///             let (span, found) = skip_through_closing_delimiter(Delimiter::Brace)
///                 .parse(stream)?;
///
///             match found {
///                 Some(closing) => {
///                     // Successfully skipped and consumed the closing brace
///                     // Emit error and continue with next block
///                     emit(MalformedBlock::new(span));
///                 }
///                 None => {
///                     // Hit EOF - block was unclosed, can't continue
///                     emit(UnclosedBlock::new(span));
///                     break;
///                 }
///             }
///         }
///     }
/// }
/// ```
///
/// ## Nested Error Recovery
///
/// ```rust,ignore
/// // Skip nested braces when inner parsing fails
/// inner_parser
///     .delimited_by(
///         just(Token::LBrace),
///         just(Token::RBrace)
///     )
///     .recover_with(via_parser(
///         // Skip everything including the closing brace
///         skip_through_closing_delimiter(Delimiter::Brace)
///             .map(|(span, _)| ErrorPlaceholder::new(span))
///     ))
/// ```
///
/// # Comparison with skip_to_closing_delimiter
///
/// ```text
/// skip_to_closing_delimiter:
///   { content } more
///            ^ positioned here (before })
///            Note: Delimiter still available for inspection
///
/// skip_through_closing_delimiter:
///   { content } more
///              ^ positioned here (after })
///              Note: Delimiter has been consumed
/// ```
///
/// **Choose `skip_to` when:**
/// - You need to inspect the delimiter token before deciding what to do
/// - You want to emit errors with the delimiter's precise span
/// - You need to validate the delimiter matches expectations
///
/// **Choose `skip_through` when:**
/// - You want to completely discard the malformed content
/// - You're implementing statement-level recovery in a block
/// - You need to quickly advance past nested structures
/// - The delimiter information isn't needed for diagnostics
///
/// # Performance Note
///
/// This function consumes tokens linearly until finding the delimiter or EOF.
/// Time complexity is O(n) where n is the number of tokens through the delimiter.
///
/// # See Also
///
/// - [`scan_closing_delimiter`]: Non-destructive check without consuming tokens
/// - [`skip_to_closing_delimiter`]: Stops before delimiter (allows inspection)
pub fn skip_through_closing_delimiter<'a, I, T, Error, E>(
  delimiter: Delimiter,
) -> impl Parser<'a, I, (Span, Option<Spanned<T>>), E> + Clone
where
  I: LogoStream<'a, T>,
  T: DelimiterToken<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let mut depth = 0;
    let before = inp.cursor();

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
            return Ok((inp.span_since(&before), Some(tok)));
          } else {
            depth -= 1;
            inp.skip();
          }
        }
        None => {
          // Reached EOF without finding closing delimiter
          return Ok((inp.span_since(&before), None));
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
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_simple_matching_paren() {
      let input = "42 )";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Paren)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_simple_matching_bracket() {
      let input = "foo ]";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Bracket)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_nested_braces() {
      let input = "{ { } } }";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_nested_parens() {
      let input = "( ( ) ( ) ) )";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Paren)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_eof_without_closing() {
      let input = "word { word";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(((0..input.len()).into(), None)));
    }

    #[test]
    fn test_eof_immediately() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(((0..input.len()).into(), None)));
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
      assert_eq!(result.into_result(), Ok(((0..input.len()).into(), None)));
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
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));

      // Second scan should still work (non-destructive)
      let parser =
        scan_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace)
          .then_ignore(any().repeated());
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
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
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      assert_eq!(span, (0..input.len() - 2).into());
      assert_eq!(skipped, 1); // Skipped 1 token (word)
      assert_eq!(tok, TestTokenKind::RBrace);
      assert_eq!(spanned.data.kind, TestTokenKind::RBrace);
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
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      assert_eq!(span, (0..input.len() - 2).into());
      assert_eq!(skipped, 3); // Skipped 3 tokens
      assert_eq!(tok, TestTokenKind::RBrace);
      assert_eq!(spanned.data.kind, TestTokenKind::RBrace);
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
      // Should skip: foo, {, bar, }, baz = 5 tokens
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      assert_eq!(span, (0..15).into());
      assert_eq!(skipped, 5);
      assert_eq!(tok, TestTokenKind::RBrace);
      assert_eq!(spanned.data.kind, TestTokenKind::RBrace);
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
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      // Should skip: {, {, {, }, }, } = 6 tokens
      assert_eq!(span, (0..input.len() - 2).into());
      assert_eq!(skipped, 6);
      assert_eq!(tok, TestTokenKind::RBrace);
      assert_eq!(spanned.data.kind, TestTokenKind::RBrace);
    }

    #[test]
    fn test_skip_eof() {
      let input = "foo bar";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(Err((2, (0..7).into()))));
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
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      assert_eq!(span, (0..0).into());
      assert_eq!(skipped, 0); // No tokens skipped
      assert_eq!(tok, TestTokenKind::RBrace);
      assert_eq!(spanned.data.kind, TestTokenKind::RBrace);
    }

    #[test]
    fn test_skip_empty_input() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(Err((0, (0..0).into()))));
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
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_skip_through_nested() {
      let input = "foo { bar } baz }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_skip_through_deeply_nested() {
      let input = "{ { { } } } }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_skip_through_eof() {
      let input = "foo bar";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(((0..7).into(), None)));
    }

    #[test]
    fn test_skip_through_immediate_match() {
      let input = "}";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }

    #[test]
    fn test_skip_through_empty_input() {
      let input = "";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_through_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      assert_eq!(result.into_result(), Ok(((0..0).into(), None)));
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

      // Should skip: (, {, } = 3 tokens, stop before )
      let (res, tok) = parser.parse(stream).into_result().unwrap();
      let (skipped, span, spanned) = res.unwrap();
      assert_eq!(span, (0..input.len() - 2).into());
      assert_eq!(skipped, 2);
      assert_eq!(tok, TestTokenKind::RParen);
      assert_eq!(spanned.data.kind, tok);
    }

    #[test]
    fn test_mixed_delimiters_paren_in_brace() {
      let input = "{ ( ) }";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Brace);
      let result = parser.parse(stream);
      // Should skip: {, (, ) = 3 tokens, stop before }
      assert_eq!(result.into_result(), Ok(Err((4, (0..7).into()))));
    }

    #[test]
    fn test_complex_nesting() {
      let input = "[ { ( ) } ( { } ) ]";
      let stream = TestTokenizer::new(input);
      let parser =
        skip_to_closing_delimiter::<_, _, TestError, extra::Err<TestError>>(Delimiter::Bracket);
      let result = parser.parse(stream);
      // Should skip: [, {, (, ), }, (, {, }, ) = 9 tokens
      assert_eq!(result.into_result(), Ok(Err((10, (0..19).into()))));
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
      assert!(matches!(result.into_result(), Ok((_, Some(_)))));
    }
  }
}
