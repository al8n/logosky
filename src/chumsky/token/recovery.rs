//! Error recovery utilities for delimiter-based parsing.
//!
//! This module provides utilities for implementing robust error recovery when parsing
//! delimiter-delimited content. These functions are the building blocks used by higher-level
//! parsers like [`DelimitedByBrace`](crate::chumsky::delimited::DelimitedByBrace) to handle
//! missing or malformed delimiters gracefully.
//!
//! # Core Recovery Functions
//!
//! ## Error Emission
//!
//! - [`emit`](crate::chumsky::token::recovery::emit): Emits an error without consuming input (eager)
//! - [`emit_with`](crate::chumsky::token::recovery::emit_with): Emits an error without consuming input (lazy, on-demand)
//!
//! ## Delimiter Scanning
//!
//! - [`scan_closing_delimiter`](crate::chumsky::token::recovery::scan_closing_delimiter): Non-destructive lookahead for closing delimiter
//! - [`skip_to_closing_delimiter`](crate::chumsky::token::recovery::skip_to_closing_delimiter): Consumes tokens up to (but not including) closing delimiter
//! - [`skip_through_closing_delimiter`](crate::chumsky::token::recovery::skip_through_closing_delimiter): Consumes tokens through (and including) closing delimiter
//!
//! # Recovery Philosophy
//!
//! These utilities follow a **three-scenario recovery pattern** for delimited content:
//!
//! 1. **Opening delimiter present**: Parse content, check for closing delimiter
//! 2. **Only closing delimiter**: Scan for it, emit error, parse bounded content
//! 3. **No delimiters**: Emit error, return `Err(span)` to prevent over-consumption
//!
//! The key principle is: **"If you don't see what you expect, don't guess."**
//! Scenario 3 returns an error instead of attempting to parse unbounded content,
//! which prevents consuming tokens from outer parsing contexts.
//!
//! # Example: Building a Delimited Parser with Recovery
//!
//! ```rust,ignore
//! use logosky::chumsky::token::recovery::{emit_with, skip_through_closing_delimiter};
//! use logosky::utils::delimiter::Delimiter;
//!
//! // Parse content delimited by braces with recovery
//! custom(|inp| {
//!     let before = inp.cursor();
//!
//!     // SCENARIO 1: Check for opening brace
//!     if let Some(Lexed::Token(t)) = inp.peek() {
//!         if t.is_brace_open() {
//!             inp.skip();
//!             let content = inp.parse(content_parser)?;
//!
//!             // Check for closing brace
//!             match inp.peek() {
//!                 Some(Lexed::Token(t)) if t.is_brace_close() => {
//!                     inp.skip();
//!                     return Ok(Ok(Delimited { span: inp.span_since(&before), content }));
//!                 }
//!                 _ => {
//!                     // Emit UnclosedBrace error
//!                     let span = inp.span_since(&before);
//!                     inp.parse(emit_with(|| UnclosedBrace::brace(span)))?;
//!                     return Ok(Ok(Delimited { span, content }));
//!                 }
//!             }
//!         }
//!     }
//!
//!     // SCENARIO 2: No opening, check for closing
//!     let checkpoint = inp.save();
//!     let (scanned, closing) = inp.parse(skip_through_closing_delimiter(Delimiter::Brace))?;
//!
//!     if closing.is_some() {
//!         inp.rewind(checkpoint);
//!         inp.parse(emit_with(|| UnopenedBrace::brace(scanned)))?;
//!         let content = inp.parse(content_parser.then_ignore(skip_until_brace_close))?;
//!         return Ok(Ok(Delimited { span: inp.span_since(&before), content }));
//!     }
//!
//!     // SCENARIO 3: No delimiters at all
//!     inp.rewind(checkpoint);
//!     inp.parse(emit_with(|| UndelimitedBrace::brace(scanned)))?;
//!     Ok(Err(inp.span_since(&before))) // Don't parse content!
//! })
//! ```
//!
//! # Why Return `Err(Span)` in Scenario 3?
//!
//! When no delimiters are found, returning `Err(span)` instead of attempting to parse
//! prevents **over-consumption** in nested contexts:
//!
//! ```text
//! {
//!   let x := 1
//!   let y := 2  // ← Missing braces, triggers Scenario 3
//!   let z := 3
//! }             // ← Outer closing brace
//! ```
//!
//! If we tried to parse unbounded content in Scenario 3, the inner parser would consume
//! `let z := 3` and the outer `}`, breaking the parent parser. By returning `Err(span)`,
//! we keep errors localized and allow outer parsers to continue normally.

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

/// Repeatedly parses tokens until finding one that passes validation, emitting errors for invalid tokens.
///
/// This parser consumes tokens from the input stream, validating each one with the provided
/// `matcher` function. Invalid tokens and lexer errors are emitted, and parsing continues.
/// When a valid token is found (matcher returns `Ok(())`), parsing stops and returns it. The
/// returned token will **NOT** be consumed (it remains in the stream for the next parser).
/// If EOF is reached without finding a valid token, returns `None`.
///
/// This is useful for error recovery scenarios where you want to skip malformed tokens
/// while reporting each error, until you find a valid synchronization point.
///
/// # Parameters
///
/// - `matcher`: A function that validates a token and returns `Result<(), Error>`:
///   - `Ok(())`: Token is valid; stop parsing and return this token
///   - `Err(error)`: Token is invalid; emit error and continue to next token
///
/// # Returns
///
/// Returns `(usize, Option<Spanned<T>>)` where:
/// - `usize`: Number of invalid tokens encountered and emitted as errors
/// - `Option<Spanned<T>>`:
///   - `Some(token)`: Found a valid token (NOT consumed, still in stream)
///   - `None`: Reached EOF without finding a valid token
///
/// # Error Behavior
///
/// For each invalid token encountered:
/// 1. **Validation failure**: `matcher` returns `Err(error)` → error is emitted, parsing continues
/// 2. **Lexer error**: Input contains a lexer error → error is emitted, parsing continues
///
/// All errors are accumulated in the parser's error state for later retrieval.
///
/// # Examples
///
/// ## Skip to Statement Boundary with Error Count
///
/// ```rust,ignore
/// use logosky::chumsky::token::recovery::emit_until_token;
///
/// // Skip malformed tokens until finding a semicolon or brace
/// let (error_count, found) = emit_until_token(|tok| {
///     match &*tok {
///         Token::Semicolon | Token::RBrace | Token::LBrace => Ok(()),
///         _ => Err(Error::UnexpectedToken(tok.span)),
///     }
/// })
/// .parse(stream)?;
///
/// if error_count > 0 {
///     println!("Skipped {} malformed tokens", error_count);
/// }
///
/// // Input: "garbage tokens ; more code"
/// // Emits errors for "garbage" and "tokens"
/// // Returns (2, Some(Semicolon))
/// ```
///
/// ## Recover from Invalid Identifier
///
/// ```rust,ignore
/// // Skip tokens until finding a valid identifier
/// let (errors, found) = emit_until_token(|tok| {
///     match &tok.data {
///         Token::Identifier(name) if !is_keyword(name) => Ok(()),
///         Token::Identifier(kw) => Err(Error::KeywordAsIdentifier(kw.clone())),
///         _ => Err(Error::ExpectedIdentifier(tok.span)),
///     }
/// })
/// .parse(stream)?;
///
/// match found {
///     Some(ident_token) => {
///         println!("Recovered after {} errors, found identifier at {:?}", errors, ident_token.span);
///         // Token is still in stream, consume it
///         let ident = identifier_parser().parse(stream)?;
///     }
///     None => {
///         return Err(Error::NoValidIdentifier { errors_emitted: errors });
///     }
/// }
///
/// // Input: "123 if else validName"
/// // Emits errors for "123", "if", "else"
/// // Returns (3, Some(Identifier("validName")))
/// ```
///
/// ## Skip to Closing Delimiter with Diagnostics
///
/// ```rust,ignore
/// // Skip to a closing delimiter for recovery
/// match emit_until_token(|tok| {
///     match &tok.data {
///         Token::RBrace | Token::RParen | Token::RBracket => Ok(()),
///         _ => Err(Error::SkippedToken(tok.span)),
///     }
/// })
/// .parse(stream)?
/// {
///     (0, Some(delim)) => {
///         // Found immediately, no errors
///         println!("Well-formed block ending at {:?}", delim.span);
///     }
///     (count, Some(delim)) => {
///         // Found after emitting errors
///         println!("Recovered at {:?} after {} errors", delim.span, count);
///     }
///     (count, None) => {
///         // Reached EOF
///         return Err(Error::UnclosedBlock { errors: count });
///     }
/// }
/// ```
///
/// ## Discarding the Tuple
///
/// ```rust,ignore
/// // When you don't need the count or token information
/// emit_until_token(|tok| {
///     match &tok.data {
///         Token::Keyword(_) => Ok(()),
///         _ => Err(Error::ExpectedKeyword(tok.span)),
///     }
/// })
/// .ignored() // Discard (count, token) tuple
/// .ignore_then(next_parser())
/// ```
///
/// # When to Use
///
/// Use `emit_until_token` when you need to:
/// - **Skip malformed tokens** while reporting each error until finding a valid synchronization point
/// - **Recover from errors** by skipping to a known-good token (semicolon, brace, keyword)
/// - **Validate conditionally** where only certain tokens are valid in a given context
///
/// For simpler cases:
/// - Use [`skip_until_token`] if you don't need to emit errors for skipped tokens
/// - Use `.filter()` if you just want to filter without error reporting
///
/// # See Also
///
/// - [`emit`]: Emit an error without consuming input
/// - [`emit_with`]: Emit an error created from a function without consuming input
/// - [`skip_until_token`](super::skip::skip_until_token): Skip tokens without emitting errors
///
/// Emits errors for each token until the matcher succeeds, optionally returning the matching token.
///
/// This helper scans forward, calling `matcher` on every token. If the matcher returns `Err(error)`,
/// the error is emitted and scanning continues. When the matcher finally returns `Ok(())`, the
/// matching token is consumed and returned. If end-of-input is reached before any token matches,
/// the parser returns `Ok(None)` without emitting an extra error (you can attach one via
/// `.validate` if desired).
///
/// Use this when you need to synchronise on the next "safe" token while reporting every skipped
/// token along the way—e.g., skipping to the next statement keyword or delimiter.
pub fn emit_until_token<'a, I, T, Error, E>(
  matcher: impl Fn(&Spanned<T>) -> Result<(), Error> + Clone + 'a,
) -> impl Parser<'a, I, (usize, Option<Spanned<T>>), E> + Clone
where
  I: LogoStream<'a, T>,
  T: Token<'a>,
  E: ParserExtra<'a, I, Error = Error> + 'a,
  Error: From<<T::Logos as Logos<'a>>::Error> + 'a,
{
  custom(move |inp| {
    let mut skipped = 0;
    loop {
      let cur = inp.save();
      let result = inp.parse(
        any()
          .validate(|t: Lexed<'_, T>, _, emitter| match t {
            Lexed::Token(tok) => match matcher(&tok) {
              Ok(()) => Some(tok),
              Err(e) => {
                emitter.emit(e);
                None
              }
            },
            Lexed::Error(e) => {
              emitter.emit(Error::from(e));
              None
            }
          })
          .or_not(),
      )?;

      match result {
        Some(Some(tok)) => {
          inp.rewind(cur);
          return Ok((skipped, Some(tok)));
        },
        Some(None) => {
          skipped += 1;
          // Validation failed, continue scanning
          continue;
        }
        None => return Ok((skipped, None)),
      }
    }
  })
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
/// the given delimiter type at depth 0, then consumes the closing delimiter as well.
/// It tracks nesting depth to find the correct matching delimiter. The input is left
/// positioned **AFTER** the closing delimiter (if found).
///
/// # Returns
///
/// Returns `(Span, Option<Spanned<T>>)` where:
/// - `Span`: The span from start position to current position (covers all scanned tokens)
/// - `Option<Spanned<T>>`:
///   - `Some(token)`: Found and consumed closing delimiter at depth 0, with its span and data
///   - `None`: Reached EOF without finding a closing delimiter
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
/// ## Basic Usage: Skip Malformed Block
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
///         let (span, closing) = skip_through_closing_delimiter(Delimiter::Brace).parse(stream)?;
///
///         match closing {
///             Some(token) => {
///                 // Successfully skipped to closing brace at token.span
///                 // Now positioned after }, continue with next statement
///                 println!("Skipped malformed block from {} to {}", span.start(), span.end());
///             }
///             None => {
///                 // Reached EOF - block was unclosed
///                 println!("Unclosed block starting at {}", span.start());
///                 break;
///             }
///         }
///     }
/// }
/// ```
///
/// ## Recovery with Position Information
///
/// ```rust,ignore
/// // Use span information for precise error reporting
/// let (scanned_span, closing_delim) = skip_through_closing_delimiter(Delimiter::Paren).parse(stream)?;
///
/// if let Some(closing_token) = closing_delim {
///     // Report what was skipped
///     errors.push(Error::new(
///         scanned_span,
///         format!("Skipped malformed content up to closing ')' at {}", closing_token.span.end())
///     ));
/// } else {
///     // Report unclosed delimiter
///     errors.push(Error::new(
///         scanned_span,
///         "Unclosed '(' - reached end of file"
///     ));
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
