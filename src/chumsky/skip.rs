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
/// # Constraints
///
/// The error type `E::Error` must implement `From<LexerError>` where `LexerError`
/// is the error type produced by the lexer. This allows lexer errors encountered
/// during recovery to be automatically converted and emitted as parser errors.
///
/// # Returns
///
/// A parser that consumes tokens until the predicate matches, producing `()`.
/// The matched token is also consumed. Any lexer errors encountered during skipping
/// are emitted to the error accumulator.
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
/// Lexer errors encountered during recovery are reported and collected. This ensures
/// comprehensive error collection - both parser-level syntax errors and lexer-level
/// lexical errors are accumulated during recovery, giving users complete diagnostics.
#[inline]
pub fn skip_until_token<'a, I, T, E, F>(predicate: F) -> impl Strategy<'a, I, (), E> + Clone
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

/// Creates a parser that skips tokens until reaching one that matches the predicate,
/// **consuming** the matching token as well.
///
/// This is useful when you want to fast-forward the token stream past a known delimiter
/// (e.g., skip until the next `)` and discard it). If you need to keep the matching token
/// for the next parser, use [`skip_until_token`] instead.
pub fn skip_until_token_inclusive<'a, I, T, E, F>(
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
pub fn skip_while_token<'a, I, T, E, F>(predicate: F) -> impl Strategy<'a, I, (), E> + Clone
where
  I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  E: chumsky::extra::ParserExtra<'a, I> + 'a,
  E::Error: From<<T::Logos as Logos<'a>>::Error>,
  F: Fn(&T) -> bool + Clone + 'a,
{
  skip_until_token(move |tok| !predicate(tok))
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
/// In most cases, [`skip_until_token`] or [`skip_until_any`] are better choices.
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
  fn skip_until_preserves_match() {
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
      .recover_with(skip_until_token(|tok: &TestToken| {
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
      .recover_with(skip_until_token_inclusive(|tok: &TestToken| {
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
  fn skip_n_tokens_limits_advance() {
    let input = "foo 123 (";
    let stream = TestStream::new(input);

    let parser = skip_n_tokens(2).ignore_then(next_kind_parser());

    let result = parser.parse(stream).into_result().expect("parse ok");
    assert_eq!(result, TestKind::LParen); // should land on the third token
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
      .recover_with(skip_while_token(|tok: &TestToken| {
        matches!(tok.kind(), TestKind::Ident)
      }))
      .ignore_then(next_kind_parser());

    let result = parser.parse(stream);
    assert!(result.errors().next().is_some());
    assert_eq!(result.output(), Some(&TestKind::LParen));
  }
}
