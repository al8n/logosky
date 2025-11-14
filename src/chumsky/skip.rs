//! Token skipping utilities for error recovery.
//!
//! This module provides generic utilities for implementing error recovery in parsers
//! via the [`Recoverable`](crate::chumsky::Recoverable) trait. These functions enable parsers
//! to skip over malformed input until reaching a "synchronization point" where parsing
//! can safely resume.
//!
//! # Design Philosophy
//!
//! Error recovery is inherently language-specific - what constitutes a safe recovery
//! point varies dramatically between languages. Rather than prescribing specific recovery
//! strategies, these utilities provide generic building blocks that work with any token
//! type. Users define recovery points through predicates, giving them full control over
//! the recovery strategy.
//!
//! # Recovery Strategies
//!
//! Different contexts require different recovery approaches:
//!
//! ## Field-Level Recovery
//!
//! Skip to the next field separator or block terminator:
//!
//! ```rust,ignore
//! skip_until_token(|tok| matches!(tok,
//!     Token::Comma | Token::Newline | Token::RBrace
//! ))
//! ```
//!
//! ## Statement-Level Recovery
//!
//! Skip to statement terminators or new statement keywords:
//!
//! ```rust,ignore
//! skip_until_token(|tok| matches!(tok,
//!     Token::Semicolon | Token::Let | Token::Fn
//! ))
//! ```
//!
//! ## Block-Level Recovery
//!
//! Use Chumsky's built-in `nested_delimiters` for balanced delimiter matching:
//!
//! ```rust,ignore
//! use chumsky::prelude::*;
//!
//! nested_delimiters(
//!     Token::LBrace,
//!     Token::RBrace,
//!     [/* nested patterns */],
//!     |span| BlockExpr::Error(span)
//! )
//! ```
//!
//! ## Top-Level Recovery
//!
//! Skip to definition keywords or end-of-file:
//!
//! ```rust,ignore
//! skip_until_token(|tok| matches!(tok,
//!     Token::Type | Token::Interface | Token::Eof
//! ))
//! ```
//!
//! # Examples
//!
//! ## GraphQL Field Definition Recovery
//!
//! ```rust,ignore
//! use logosky::chumsky::{Recoverable, skip_until_token};
//!
//! impl<...> Recoverable<...> for FieldDefinition {
//!     fn parser<E>() -> impl Parser<...> {
//!         name_parser()
//!             .then(colon_parser().or_not())
//!             .then(type_parser().or_not())
//!             .try_map_with(|(name, colon, ty), exa| {
//!                 // Validate and collect errors
//!                 let mut errors = IncompleteSyntax::new(...);
//!                 if colon.is_none() { errors.add(Component::Colon); }
//!                 if ty.is_none() { errors.add(Component::Type); }
//!
//!                 if errors.is_empty() {
//!                     Ok(FieldDefinition { name, ty: ty.unwrap() })
//!                 } else {
//!                     Err(Error::from(errors))
//!                 }
//!             })
//!             .recover_with(via_parser(
//!                 skip_until_token(|tok| matches!(tok,
//!                     SyntacticToken::Punctuator(Punctuator::Comma) |
//!                     SyntacticToken::Punctuator(Punctuator::Newline) |
//!                     SyntacticToken::Punctuator(Punctuator::RBrace)
//!                 ))
//!                 .map_with(|_, exa| FieldDefinition::placeholder(exa.span()))
//!             ))
//!     }
//! }
//! ```
//!
//! ## JSON Object Recovery
//!
//! ```rust,ignore
//! impl<...> Recoverable<...> for JsonObject {
//!     fn parser<E>() -> impl Parser<...> {
//!         key_value_pairs()
//!             .recover_with(via_parser(
//!                 skip_until_token(|tok| matches!(tok,
//!                     JsonToken::Comma |   // Next key-value
//!                     JsonToken::RBrace |  // End of object
//!                     JsonToken::Eof       // End of input
//!                 ))
//!                 .map_with(|_, exa| JsonObject::empty(exa.span()))
//!             ))
//!     }
//! }
//! ```
//!
//! ## Multiple Recovery Points
//!
//! ```rust,ignore
//! use logosky::chumsky::skip_until_token;
//!
//! // Skip until any of: separator, block end, or definition start
//! skip_until_token(|tok| {
//!     matches!(tok, Token::Comma | Token::Newline) ||
//!     matches!(tok, Token::RBrace | Token::RBracket) ||
//!     matches!(tok, Token::Type | Token::Interface)
//! })
//! ```

use crate::{Lexed, Token};
use chumsky::{Parser, prelude::*, recovery::Strategy};
use logos::{Logos, Source};

use super::LogoStream;

/// Creates a recovery strategy that skips tokens until a predicate matches, leaving the matching token for the next parser.
///
/// This is a **recovery strategy** version of [`skip_until_token`] that can be used
/// directly with Chumsky's `.recover_with()` combinator without needing `via_parser()`.
///
/// # Strategy vs Parser
///
/// Chumsky provides two ways to perform error recovery:
///
/// 1. **Strategy** (this function): Use directly with `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(skip_until_token_strategy(predicate))
///    ```
///
/// 2. **Parser** ([`skip_until_token`]): Wrap with `via_parser()` for `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(via_parser(skip_until_token(predicate)))
///    ```
///
/// Both approaches are functionally equivalent. Use strategies for slightly cleaner code
/// when you don't need to transform the recovery result.
///
/// # Recovery Strategy
///
/// The predicate function decides what constitutes a "recovery point" - a token
/// where parsing can safely resume. Common patterns include:
///
/// - **Field recovery**: Skip until commas, newlines, or closing braces
/// - **Statement recovery**: Skip until semicolons or statement keywords
/// - **Top-level recovery**: Skip until definition keywords or EOF
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies recovery points
///
/// # Behavior
///
/// - Skips tokens until the predicate returns `true`
/// - The matching token is **NOT** consumed (left for next parser to use)
/// - Lexer errors encountered during skipping are emitted
/// - Returns `()` when a match is found or end-of-input is reached
///
/// # Returns
///
/// A recovery strategy that consumes tokens until the predicate matches.
/// The matching token remains in the stream for the next parser.
///
/// # Examples
///
/// ## Field-Level Recovery (Direct Strategy)
///
/// ```rust,ignore
/// use logosky::chumsky::skip_until_token_strategy;
///
/// impl Recoverable<...> for FieldDefinition {
///     fn parser<E>() -> impl Parser<...> {
///         field_parser()
///             // Use strategy directly with recover_with
///             .recover_with(skip_until_token_strategy(|tok| matches!(tok,
///                 Token::Comma | Token::Newline | Token::RBrace
///             )))
///     }
/// }
/// ```
///
/// ## Statement Recovery
///
/// ```rust,ignore
/// statement_parser()
///     .recover_with(skip_until_token_strategy(|tok| matches!(tok,
///         Token::Semicolon | Token::Let | Token::Fn
///     )))
/// ```
///
/// ## Comparison: Strategy vs Parser
///
/// ```rust,ignore
/// // Using strategy (direct)
/// parser.recover_with(skip_until_token_strategy(predicate))
///
/// // Using parser (requires via_parser wrapper)
/// parser.recover_with(via_parser(
///     skip_until_token(predicate)
///         .map_with(|_, exa| Placeholder::new(exa.span()))
/// ))
///
/// // Use parser version when you need to transform the result
/// // Use strategy version for simpler cases
/// ```
///
/// # See Also
///
/// - [`skip_until_token`]: Parser version that allows result transformation
/// - [`skip_until_token_inclusive_strategy`]: Strategy that consumes the matching token
/// - [`skip_while_token_strategy`]: Strategy that skips while predicate matches
#[inline]
pub fn skip_until_token_strategy<'a, I, T, E, F>(
  predicate: F,
) -> impl Strategy<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  let pred_clone = predicate.clone();
  chumsky::prelude::skip_until(
    any()
      .validate(move |t: Lexed<'_, T>, _span, emitter| match t {
        Lexed::Token(spanned_tok) => {
          if !predicate(&*spanned_tok) {
            Some(())
          } else {
            None
          }
        }
        Lexed::Error(e) => {
          emitter.emit(E::Error::from(e));
          None
        }
      })
      .ignored(),
    any()
      .filter(move |t: &Lexed<'_, T>| match t {
        Lexed::Token(spanned_tok) => pred_clone(spanned_tok),
        Lexed::Error(_) => false,
      })
      .ignored()
      .rewind(),
    || (),
  )
}

/// Creates a recovery strategy that skips tokens until a predicate matches, **consuming** the matching token.
///
/// This is a **recovery strategy** version of [`skip_until_token_inclusive`] that can be used
/// directly with Chumsky's `.recover_with()` combinator without needing `via_parser()`.
///
/// # Strategy vs Parser
///
/// Chumsky provides two ways to perform error recovery:
///
/// 1. **Strategy** (this function): Use directly with `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(skip_until_token_inclusive_strategy(predicate))
///    ```
///
/// 2. **Parser** ([`skip_until_token_inclusive`]): Wrap with `via_parser()` for `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(via_parser(skip_until_token_inclusive(predicate)))
///    ```
///
/// Both approaches are functionally equivalent. Use strategies for slightly cleaner code
/// when you don't need to transform the recovery result.
///
/// # When to Use This
///
/// Use this when you want to skip past a delimiter and discard it entirely. For example:
/// - Skip until `;` and consume it (don't need the semicolon)
/// - Skip until `)` and consume it (closing paren is not needed)
/// - Skip until `}` and consume it (block end is handled)
///
/// If you need to preserve the matching token for the next parser, use
/// [`skip_until_token_strategy`] instead.
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies recovery points
///
/// # Behavior
///
/// - Skips tokens until the predicate returns `true`
/// - The matching token **IS** consumed (discarded from the stream)
/// - Lexer errors encountered during skipping are emitted
/// - Returns `()` when a match is consumed or end-of-input is reached
///
/// # Returns
///
/// A recovery strategy that consumes tokens including the matching one.
///
/// # Examples
///
/// ## Skip Past Semicolons
///
/// ```rust,ignore
/// use logosky::chumsky::skip_until_token_inclusive_strategy;
///
/// // Skip until semicolon and consume it
/// statement_parser()
///     .recover_with(skip_until_token_inclusive_strategy(|tok| matches!(tok,
///         Token::Semicolon
///     )))
/// ```
///
/// ## Skip Past Closing Delimiters
///
/// ```rust,ignore
/// // Skip until closing paren and consume it
/// expr_parser()
///     .recover_with(skip_until_token_inclusive_strategy(|tok| matches!(tok,
///         Token::RParen | Token::RBrace | Token::RBracket
///     )))
/// ```
///
/// ## Comparison: Inclusive vs Non-Inclusive
///
/// ```rust,ignore
/// // Non-inclusive: matching token is preserved
/// skip_until_token_strategy(|tok| tok.is_semicolon())
/// // After recovery, semicolon is still in the stream
///
/// // Inclusive: matching token is consumed
/// skip_until_token_inclusive_strategy(|tok| tok.is_semicolon())
/// // After recovery, semicolon has been consumed
/// ```
///
/// # See Also
///
/// - [`skip_until_token_inclusive`]: Parser version that allows result transformation
/// - [`skip_until_token_strategy`]: Strategy that preserves the matching token
/// - [`skip_while_token_strategy`]: Strategy that skips while predicate matches
pub fn skip_until_token_inclusive_strategy<'a, I, T, E, F>(
  predicate: F,
) -> impl Strategy<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  let pred_clone = predicate.clone();
  chumsky::prelude::skip_until(
    any()
      .validate(move |t: Lexed<'_, T>, _span, emitter| match t {
        Lexed::Token(spanned_tok) => {
          if !predicate(&*spanned_tok) {
            Some(())
          } else {
            None
          }
        }
        Lexed::Error(e) => {
          emitter.emit(E::Error::from(e));
          None
        }
      })
      .ignored(),
    any()
      .filter(move |t: &Lexed<'_, T>| match t {
        Lexed::Token(spanned_tok) => pred_clone(spanned_tok),
        Lexed::Error(_) => false,
      })
      .ignored(),
    || (),
  )
}

/// Creates a parser that skips tokens until reaching one that matches the predicate,
/// **consuming** the matching token as well.
///
/// This is useful when you want to fast-forward the token stream past a known delimiter
/// (e.g., skip until the next `)` and discard it). If you need to keep the matching token
/// for the next parser, use [`skip_until_token`] instead.
pub fn skip_until_token_inclusive<'a, I, T, E, F>(predicate: F) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  custom(move |inp| {
    while let Some(lexed) = inp.peek() {
      match lexed {
        Lexed::Token(spanned_tok) => {
          if predicate(&spanned_tok) {
            inp.skip(); // Consume the matching token
            return Ok(());
          }
          inp.skip();
        }
        Lexed::Error(_) => {
          // inp does not have an emit method, so we use a validate parser to emit the error
          inp.parse(any().validate(|tok, _, emitter| {
            if let Lexed::Error(err) = tok {
              emitter.emit(E::Error::from(err));
            }
          }))?;
        }
      }
    }
    Ok(())
  })
}

/// Creates a recovery strategy that skips tokens while a predicate matches, stopping at the first non-match.
///
/// This is a **recovery strategy** version of [`skip_while_token`] that can be used
/// directly with Chumsky's `.recover_with()` combinator without needing `via_parser()`.
///
/// # Strategy vs Parser
///
/// Chumsky provides two ways to perform error recovery:
///
/// 1. **Strategy** (this function): Use directly with `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(skip_while_token_strategy(predicate))
///    ```
///
/// 2. **Parser** ([`skip_while_token`]): Wrap with `via_parser()` for `.recover_with()`
///    ```rust,ignore
///    parser.recover_with(via_parser(skip_while_token(predicate)))
///    ```
///
/// Both approaches are functionally equivalent. Use strategies for slightly cleaner code
/// when you don't need to transform the recovery result.
///
/// # When to Use This
///
/// This is the inverse of [`skip_until_token_strategy`] - it skips tokens **while** they
/// match the predicate, stopping when a non-matching token is found:
///
/// - Skip whitespace or comments during recovery
/// - Skip a sequence of specific token types
/// - Consume "noise" tokens before attempting recovery
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies tokens to skip
///
/// # Behavior
///
/// - Skips tokens while the predicate returns `true`
/// - Stops at the first token where the predicate returns `false`
/// - The non-matching token is **NOT** consumed
/// - Lexer errors encountered during skipping are emitted
///
/// # Returns
///
/// A recovery strategy that consumes matching tokens, stopping at the first non-match.
/// The non-matching token is left for the next parser.
///
/// # Examples
///
/// ## Skip Whitespace Before Recovery
///
/// ```rust,ignore
/// use logosky::chumsky::skip_while_token_strategy;
///
/// // Skip all whitespace tokens before attempting recovery
/// parser.recover_with(skip_while_token_strategy(|tok| matches!(tok,
///     Token::Whitespace | Token::Newline
/// )))
/// ```
///
/// ## Skip Comment Tokens
///
/// ```rust,ignore
/// // Skip all comments until finding actual code
/// parser.recover_with(skip_while_token_strategy(|tok| tok.is_comment()))
/// ```
///
/// ## Skip Invalid Tokens
///
/// ```rust,ignore
/// // Skip tokens marked as errors by the lexer
/// parser.recover_with(skip_while_token_strategy(|tok| tok.is_error()))
/// ```
///
/// ## Comparison: While vs Until
///
/// ```rust,ignore
/// // These are equivalent:
/// skip_while_token_strategy(|tok| tok.is_whitespace())
/// skip_until_token_strategy(|tok| !tok.is_whitespace())
///
/// // skip_while: "keep going WHILE this is true"
/// // skip_until: "keep going UNTIL this is true"
/// ```
///
/// # See Also
///
/// - [`skip_while_token`]: Parser version that allows result transformation
/// - [`skip_until_token_strategy`]: Strategy that skips until predicate matches
/// - [`skip_until_token_inclusive_strategy`]: Strategy that consumes the matching token
#[inline]
pub fn skip_while_token_strategy<'a, I, T, E, F>(
  predicate: F,
) -> impl Strategy<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  skip_until_token_strategy(move |tok| !predicate(tok))
}

/// Creates a parser that skips at most N tokens.
///
/// This is useful for fixed-distance recovery when you know at most how many
/// tokens to skip. Less common than predicate-based recovery but useful in
/// specific scenarios.
///
/// # Parameters
///
/// - `n`: The at most number of tokens to skip
///
/// # Returns
///
/// A parser that consumes at most `n` tokens, producing `()`.
///
/// # Examples
///
/// ## Fixed Recovery Distance
///
/// ```rust,ignore
/// use logosky::chumsky::skip_n_tokens;
///
/// // Skip exactly 3 tokens after encountering an error
/// field_parser()
///     .recover_with(via_parser(
///         skip_n_tokens(3)
///             .map_with(|_, exa| Field::placeholder(exa.span()))
///     ))
/// ```
///
/// ## Skip Known Invalid Sequence
///
/// ```rust,ignore
/// // If we know an error produces exactly 2 invalid tokens, skip them
/// skip_n_tokens(2).then(resume_parsing())
/// ```
///
/// # Note
///
/// This function is less flexible than predicate-based recovery and should
/// only be used when the recovery distance is truly fixed and known in advance.
/// In most cases, [`skip_until_token`] or [`skip_while_token`] are better choices.
#[inline]
pub fn skip_n_tokens<'a, I, T, E>(n: usize) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
{
  any()
    .validate(|lexed: Lexed<'a, T>, _span, emitter| {
      match lexed {
        Lexed::Token(_) => Some(()),
        Lexed::Error(err) => {
          // Emit lexer error during recovery
          emitter.emit(E::Error::from(err));
          Some(()) // Continue skipping after emitting error
        }
      }
    })
    .repeated()
    .at_most(n)
    .ignored()
}

/// Creates a parser that skips tokens until a predicate matches, leaving the matching token for the next parser.
///
/// This is the main recovery utility for implementing error recovery in parsers.
/// It continues consuming tokens until finding one that matches the given predicate,
/// then stops **without consuming** the matching token, leaving it available for
/// subsequent parsers.
///
/// # Recovery Strategy
///
/// The predicate function decides what constitutes a "recovery point" - a token
/// where parsing can safely resume. Common patterns include:
///
/// - **Field recovery**: Skip until commas, newlines, or closing braces
/// - **Statement recovery**: Skip until semicolons or statement keywords
/// - **Top-level recovery**: Skip until definition keywords or EOF
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies recovery points
///
/// # Behavior
///
/// - Skips tokens until the predicate returns `true`
/// - The matching token is **NOT** consumed (use [`skip_until_token_inclusive`] to consume it)
/// - Lexer errors encountered during skipping are emitted
/// - Returns `Ok(())` when a match is found or end-of-input is reached
///
/// # Returns
///
/// A parser that consumes tokens until the predicate matches, producing `()`.
/// The matching token remains in the stream for the next parser.
///
/// # Examples
///
/// ## Field-Level Recovery
///
/// ```rust,ignore
/// use logosky::chumsky::skip_until_token;
///
/// // Skip until finding a comma, newline, or closing brace
/// // The matching token is preserved for the next parser
/// field_parser()
///     .recover_with(via_parser(
///         skip_until_token(|tok| matches!(tok,
///             Token::Comma | Token::Newline | Token::RBrace
///         ))
///         .map_with(|_, exa| Field::placeholder(exa.span()))
///     ))
/// ```
///
/// ## Statement Recovery
///
/// ```rust,ignore
/// // Skip until semicolon or statement keyword
/// // The keyword is preserved so it can start the next statement
/// skip_until_token(|tok| matches!(tok,
///     Token::Semicolon | Token::Let | Token::Fn | Token::Return
/// ))
/// ```
///
/// ## Top-Level Recovery
///
/// ```rust,ignore
/// // Skip until definition keyword or EOF
/// skip_until_token(|tok| matches!(tok,
///     Token::Type | Token::Interface | Token::Enum | Token::Eof
/// ))
/// ```
///
/// # See Also
///
/// - [`skip_until_token_inclusive`]: Same behavior but consumes the matching token
/// - [`skip_until_token_strategy`]: Strategy version for use with `recover_with`
/// - [`skip_while_token`]: Skip while predicate matches (inverse behavior)
#[inline]
pub fn skip_until_token<'a, I, T, E, F>(predicate: F) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  custom(move |inp| {
    while let Some(lexed) = inp.peek() {
      match lexed {
        Lexed::Token(spanned_tok) => {
          if predicate(&spanned_tok) {
            return Ok(());
          }
          inp.skip();
        }
        Lexed::Error(_) => {
          // inp does not have an emit method, so we use a validate parser to emit the error
          inp.parse(any().validate(|tok, _, emitter| {
            if let Lexed::Error(err) = tok {
              emitter.emit(E::Error::from(err));
            }
          }))?;
        }
      }
    }
    Ok(())
  })
}

/// Creates a parser that skips tokens while a predicate matches, stopping at the first non-match.
///
/// This is the inverse of [`skip_until_token`] - it continues skipping tokens
/// as long as they match the predicate, stopping when a non-matching token is
/// found. The non-matching token is **NOT** consumed.
///
/// # Use Cases
///
/// - Skip whitespace or comments during recovery
/// - Skip a known sequence of tokens
/// - Consume tokens of a specific type until finding something different
/// - Skip "noise" tokens before attempting recovery
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies tokens to skip
///
/// # Behavior
///
/// - Skips tokens while the predicate returns `true`
/// - Stops at the first token where the predicate returns `false`
/// - The non-matching token is **NOT** consumed
/// - Lexer errors encountered during skipping are emitted
///
/// # Returns
///
/// A parser that consumes matching tokens, stopping at the first non-match,
/// producing `()`. The non-matching token is left for the next parser.
///
/// # Examples
///
/// ## Skip Whitespace Before Recovery
///
/// ```rust,ignore
/// use logosky::chumsky::skip_while_token;
///
/// // Skip all whitespace before attempting recovery
/// skip_while_token(|tok| matches!(tok, Token::Whitespace | Token::Newline))
///     .ignore_then(recovery_parser())
/// ```
///
/// ## Skip Comments
///
/// ```rust,ignore
/// // Skip comment tokens until finding actual code
/// skip_while_token(|tok| tok.is_comment())
///     .ignore_then(statement_parser())
/// ```
///
/// ## Skip Invalid Tokens
///
/// ```rust,ignore
/// // Skip tokens marked as errors by the lexer
/// skip_while_token(|tok| tok.is_error())
///     .ignore_then(resume_parsing())
/// ```
///
/// ## Skip Specific Token Types
///
/// ```rust,ignore
/// // Skip all number tokens until finding something else
/// skip_while_token(|tok| matches!(tok, Token::Number(_)))
/// ```
///
/// # Comparison with skip_until_token
///
/// ```rust,ignore
/// // These are equivalent:
/// skip_while_token(|tok| tok.is_whitespace())
/// skip_until_token(|tok| !tok.is_whitespace())
///
/// // skip_while: "keep going while this is true"
/// // skip_until: "keep going until this is true"
/// ```
///
/// # See Also
///
/// - [`skip_until_token`]: Skip until predicate matches (inverse behavior)
/// - [`skip_while_token_strategy`]: Strategy version for use with `recover_with`
/// - [`skip_n_tokens`]: Skip a fixed number of tokens
#[inline]
pub fn skip_while_token<'a, I, T, E, F>(predicate: F) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  skip_until_token(move |tok| !predicate(tok))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{Lexed, Token, Tokenizer};
  use chumsky::{error::EmptyErr, extra};
  use logos::Logos;

  #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
  struct Error;

  impl From<Error> for EmptyErr {
    fn from(_: Error) -> Self {
      EmptyErr::default()
    }
  }

  #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
  #[logos(
    skip r"[ \t\r\n]+",
    error = Error
  )]
  enum RawToken {
    #[regex(r"[a-zA-Z]+")]
    Ident,
    #[regex(r"[0-9]+")]
    Number,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  enum TestKind {
    Ident,
    Number,
    LParen,
    RParen,
  }

  #[derive(Debug, Clone, Copy, PartialEq, Eq)]
  struct TestToken {
    kind: TestKind,
  }

  impl From<RawToken> for TestToken {
    fn from(value: RawToken) -> Self {
      let kind = match value {
        RawToken::Ident => TestKind::Ident,
        RawToken::Number => TestKind::Number,
        RawToken::LParen => TestKind::LParen,
        RawToken::RParen => TestKind::RParen,
      };
      Self { kind }
    }
  }

  impl Token<'_> for TestToken {
    type Char = char;
    type Kind = TestKind;
    type Logos = RawToken;

    fn kind(&self) -> Self::Kind {
      self.kind
    }
  }

  type TestStream<'a> = Tokenizer<'a, TestToken>;

  fn next_kind_parser<'a>()
  -> impl Parser<'a, TestStream<'a>, TestKind, extra::Err<EmptyErr>> + Clone {
    any().try_map(|lexed: Lexed<'_, TestToken>, _| match lexed {
      Lexed::Token(tok) => Ok(tok.kind()),
      Lexed::Error(e) => Err(e.into()),
    })
  }

  #[test]
  fn skip_until_preserves_match_strategy() {
    let input = "123 123 123 foo (";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::Ident {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(skip_until_token_strategy(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      }))
      .ignore_then(next_kind_parser().then(next_kind_parser()));

    let result = parser.parse(stream);
    let output = result.output();
    assert_eq!(output, Some(&(TestKind::Ident, TestKind::LParen)));
    let mut errs = result.errors();
    assert!(errs.next().is_some());
    assert!(errs.next().is_none());
  }

  #[test]
  fn skip_until_preserves_match() {
    let input = "123 123 123 foo";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::Ident {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(via_parser(skip_until_token(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      })))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    let output = result.output();
    assert_eq!(output, Some(&TestKind::Ident));
    let mut errs = result.errors();
    assert!(errs.next().is_some());
    assert!(errs.next().is_none());
  }

  #[test]
  fn skip_until_inclusive_consumes_match_strategy() {
    let input = "123 123 123 foo (";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::Ident {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(skip_until_token_inclusive_strategy(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      }))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    let output = result.output();
    assert_eq!(output, Some(&TestKind::LParen));
    let mut errs = result.errors();
    assert!(errs.next().is_some());
    assert!(errs.next().is_none());
  }

  #[test]
  fn skip_until_inclusive_consumes_match() {
    let input = "123 123 123 foo (";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::Ident {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(via_parser(skip_until_token_inclusive(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      })))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    let output = result.output();
    assert_eq!(output, Some(&TestKind::LParen));
    let mut errs = result.errors();
    assert!(errs.next().is_some());
    assert!(errs.next().is_none());
  }

  #[test]
  fn skip_n_tokens_limits_advance() {
    let input = "foo 123 (";
    let stream = TestStream::new(input);

    let parser = skip_n_tokens(2).ignore_then(next_kind_parser());

    let result = parser.parse(stream).into_result().expect("parse ok");
    assert_eq!(result, TestKind::LParen); // should land on the third token
  }

  #[test]
  fn skip_while_tokens_stops_on_nonmatch_strategy() {
    let input = "foo foo (";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::LParen {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(skip_while_token_strategy(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      }))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    assert!(result.errors().next().is_some());
    assert_eq!(result.output(), Some(&TestKind::LParen));
  }

  #[test]
  fn skip_while_tokens_stops_on_nonmatch() {
    let input = "foo foo (";
    let stream = TestStream::new(input);

    let parser = any::<_, extra::Err<EmptyErr>>()
      .try_map(|tok: Lexed<'_, TestToken>, _| match tok {
        Lexed::Token(t) => {
          if t.kind() == TestKind::LParen {
            Ok(t.kind())
          } else {
            Err(Error.into())
          }
        }
        Lexed::Error(e) => Err(e.into()),
      })
      .ignored()
      .recover_with(via_parser(skip_while_token(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      })))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    assert!(result.errors().next().is_some());
    assert_eq!(result.output(), Some(&TestKind::LParen));
  }
}
