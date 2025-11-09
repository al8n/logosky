//! Token skipping utilities for error recovery.
//!
//! This module provides generic utilities for implementing error recovery in parsers
//! via the [`Recoverable`](super::Recoverable) trait. These functions enable parsers
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
//! use logosky::chumsky::skip_until_any;
//!
//! // Skip until any of: separator, block end, or definition start
//! skip_until_any([
//!     |tok| matches!(tok, Token::Comma | Token::Newline),
//!     |tok| matches!(tok, Token::RBrace | Token::RBracket),
//!     |tok| matches!(tok, Token::Type | Token::Interface),
//! ])
//! ```

use crate::{Lexed, Token};
use chumsky::{prelude::*, Parser};
use logos::{Logos, Source};

use super::LogoStream;

/// Creates a parser that skips tokens until a predicate matches.
///
/// This is a generic recovery utility for implementing [`Recoverable`](super::Recoverable)
/// parsers. It continues consuming tokens until finding one that matches the given
/// predicate, then stops. The matched token is consumed.
///
/// # Recovery Strategy
///
/// The predicate function decides what constitutes a "recovery point" - a token
/// where parsing can safely resume. This is entirely language and context dependent:
///
/// - **Field recovery**: Skip until commas, newlines, or closing braces
/// - **Statement recovery**: Skip until semicolons or statement keywords
/// - **Block recovery**: Skip until matching closing delimiters
/// - **Top-level recovery**: Skip until definition keywords or EOF
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies recovery points
///
/// # Returns
///
/// A parser that consumes tokens until the predicate matches, producing `()`.
/// The matched token is also consumed.
///
/// # Examples
///
/// ## Field-Level Recovery (GraphQL)
///
/// ```rust,ignore
/// use logosky::chumsky::{Recoverable, skip_until_token};
///
/// impl Recoverable<...> for FieldDefinition {
///     fn parser<E>() -> impl Parser<...> {
///         field_parser()
///             .recover_with(via_parser(
///                 skip_until_token(|tok| matches!(tok,
///                     Token::Comma | Token::Newline | Token::RBrace
///                 ))
///                 .map_with(|_, exa| FieldDefinition::placeholder(exa.span()))
///             ))
///     }
/// }
/// ```
///
/// ## Statement Recovery (Rust-like)
///
/// ```rust,ignore
/// // Skip until semicolon or new statement keyword
/// skip_until_token(|tok| matches!(tok,
///     Token::Semicolon | Token::Let | Token::Fn
/// ))
/// ```
///
/// ## Top-Level Definition Recovery
///
/// ```rust,ignore
/// // Skip until the next definition keyword or EOF
/// skip_until_token(|tok| matches!(tok,
///     Token::Type | Token::Interface | Token::Enum | Token::Eof
/// ))
/// ```
///
/// # Behavior with Lexer Errors
///
/// Lexer errors encountered during recovery are silently skipped. This allows
/// recovery to continue even when the input contains both syntax errors (parser level)
/// and lexical errors (lexer level).
#[inline]
pub fn skip_until_token<'a, I, T, E, F>(predicate: F) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  F: Fn(&T) -> bool + Clone + 'a,
{
  let pred_clone = predicate.clone();

  // Skip tokens until we find one that matches the predicate
  any()
    .filter(move |lexed: &Lexed<'a, T>| match lexed {
      Lexed::Token(spanned_tok) => !predicate(&**spanned_tok),
      Lexed::Error(_) => true, // Skip lexer errors too
    })
    .repeated()
    // Then consume the matching token
    .then(
      any().filter(move |lexed: &Lexed<'a, T>| match lexed {
        Lexed::Token(spanned_tok) => pred_clone(&**spanned_tok),
        Lexed::Error(_) => false,
      })
    )
    .ignored()
}

/// Creates a parser that skips tokens until any of multiple predicates match.
///
/// This is a convenience wrapper around [`skip_until_token`] that accepts multiple
/// predicates and stops when any of them matches. Useful when recovery points fall
/// into multiple categories or when you want to compose recovery strategies.
///
/// # Type Parameters
///
/// - `F`: Predicate function type `Fn(&T) -> bool`
/// - `N`: Number of predicates (inferred from array size)
///
/// # Returns
///
/// A parser that consumes tokens until any predicate matches, producing `()`.
///
/// # Examples
///
/// ## Multiple Recovery Categories
///
/// ```rust,ignore
/// use logosky::chumsky::skip_until_any;
///
/// // Skip until separator OR block end OR definition start
/// skip_until_any([
///     |tok| matches!(tok, Token::Comma | Token::Newline),
///     |tok| matches!(tok, Token::RBrace | Token::RBracket),
///     |tok| matches!(tok, Token::Type | Token::Interface),
/// ])
/// ```
///
/// ## Context-Dependent Recovery
///
/// ```rust,ignore
/// // Different recovery points for different contexts
/// let field_recovery = |tok| matches!(tok, Token::Comma | Token::RBrace);
/// let stmt_recovery = |tok| matches!(tok, Token::Semicolon);
/// let eof_recovery = |tok| matches!(tok, Token::Eof);
///
/// skip_until_any([field_recovery, stmt_recovery, eof_recovery])
/// ```
///
/// ## Layered Recovery Strategy
///
/// ```rust,ignore
/// // Try local recovery first, then broader recovery
/// skip_until_any([
///     // Local: next sibling element
///     |tok| tok.is_separator(),
///     // Medium: end of current block
///     |tok| tok.is_block_terminator(),
///     // Broad: next top-level definition
///     |tok| tok.is_definition_start(),
///     // Last resort: EOF
///     |tok| tok.is_eof(),
/// ])
/// ```
#[inline]
pub fn skip_until_any<'a, I, T, E, F, const N: usize>(
  predicates: [F; N],
) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  F: Fn(&T) -> bool + Clone + 'a,
{
  skip_until_token(move |tok| predicates.iter().any(|pred| pred(tok)))
}

/// Creates a parser that skips tokens while they match a predicate.
///
/// This is the inverse of [`skip_until_token`] - it continues skipping tokens
/// as long as they match the predicate, stopping when a non-matching token is
/// found. The non-matching token is NOT consumed.
///
/// # Use Cases
///
/// - Skip whitespace or comments before recovery
/// - Skip a known sequence of invalid tokens
/// - Consume tokens of a specific type during recovery
///
/// # Type Parameters
///
/// - `F`: Predicate function `Fn(&T) -> bool` that identifies tokens to skip
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
/// // Skip all whitespace tokens before attempting recovery
/// skip_while_token(|tok| matches!(tok, Token::Whitespace | Token::Newline))
///     .then(attempt_recovery())
/// ```
///
/// ## Skip Error Tokens
///
/// ```rust,ignore
/// // Skip tokens marked as errors by the lexer
/// skip_while_token(|tok| tok.is_error())
/// ```
///
/// ## Consume Invalid Characters
///
/// ```rust,ignore
/// // Skip until we find a valid token
/// skip_while_token(|tok| !tok.is_valid())
/// ```
#[inline]
pub fn skip_while_token<'a, I, T, E, F>(predicate: F) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  F: Fn(&T) -> bool + Clone + 'a,
{
  skip_until_token(move |tok| !predicate(tok))
}

/// Creates a parser that skips exactly N tokens.
///
/// This is useful for fixed-distance recovery when you know exactly how many
/// tokens to skip. Less common than predicate-based recovery but useful in
/// specific scenarios.
///
/// # Parameters
///
/// - `n`: The exact number of tokens to skip
///
/// # Returns
///
/// A parser that consumes exactly `n` tokens, producing `()`.
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
/// In most cases, [`skip_until_token`] or [`skip_until_any`] are better choices.
#[inline]
pub fn skip_n_tokens<'a, I, T, E>(n: usize) -> impl Parser<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
{
  any().ignored().repeated().exactly(n).ignored()
}
