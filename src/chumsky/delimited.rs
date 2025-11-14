//! Helper AST types for delimiter-based content recovery.
//!
//! This module provides generic delimited content types that implement comprehensive
//! error recovery for paired delimiters (braces, parentheses, brackets, angle brackets).
//!
//! Each delimiter type follows a **two-tier recovery philosophy**:
//! - **Structural level**: Handle delimiter presence/absence errors
//! - **Content level**: Delegate content-specific errors to the content parser
//!
//! # Available Types
//!
//! - [`DelimitedByBrace`](crate::chumsky::delimited::DelimitedByBrace): Content enclosed by `{` and `}`
//! - [`DelimitedByParen`](crate::chumsky::delimited::DelimitedByParen): Content enclosed by `(` and `)`
//! - [`DelimitedByBracket`](crate::chumsky::delimited::DelimitedByBracket): Content enclosed by `[` and `]`
//! - [`DelimitedByAngle`](crate::chumsky::delimited::DelimitedByAngle): Content enclosed by `<` and `>`

use core::marker::PhantomData;

use crate::{
  Lexed, LogoStream, Logos, PunctuatorToken, Source, Token,
  chumsky::{
    Parser,
    extra::ParserExtra,
    prelude::*,
    token::{
      punct::{
        angle_close, angle_open, brace_close, brace_open, bracket_close, bracket_open, paren_close,
        paren_open,
      },
      recovery::{emit_with, skip_through_closing_delimiter},
    },
  },
  error::{
    UnclosedAngle, UnclosedBrace, UnclosedBracket, UnclosedParen, UndelimitedAngle,
    UndelimitedBrace, UndelimitedBracket, UndelimitedParen, UnexpectedEot, UnexpectedToken,
    UnopenedAngle, UnopenedBrace, UnopenedBracket, UnopenedParen,
  },
  syntax::Language,
  utils::{
    Span,
    cmp::Equivalent,
    delimiter::{Delimiter, LAngle, LBrace, LBracket, LParen, RAngle, RBrace, RBracket, RParen},
  },
};

/// Generates a delimited content type with comprehensive error recovery.
///
/// This macro generates all necessary types, methods, and parsers for a delimited
/// content type. It reduces code duplication by providing a declarative way to define
/// delimiter-specific types with identical recovery logic.
macro_rules! delimited_by {
  (
    $(#[$meta:meta])*
    $name:ident {
      delimiter_name: $delim_name:literal,
      delimiter_open: $delim_open:literal,
      delimiter_close: $delim_close:literal,
      delimiter_enum: $delim_enum:ident,
      delimiter_method: $delim_method:ident,
      left_delim_type: $left_type:ident,
      right_delim_type: $right_type:ident,
      open_fn: $open_fn:ident,
      close_fn: $close_fn:ident,
      check_open_fn: $check_open_fn:ident,
      unclosed_error: $unclosed_error:ident,
      unopened_error: $unopened_error:ident,
      undelimited_error: $undelimited_error:ident,
    }
  ) => {
    $(#[$meta])*
    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
    pub struct $name<Content, Lang> {
      span: Span,
      content: Content,
      _m: PhantomData<Lang>,
    }

    impl<Content, Lang> $name<Content, Lang> {
      #[doc = concat!("Creates a new ", $delim_name, "-delimited content.")]
      ///
      /// # Parameters
      ///
      /// - `span`: The span covering the entire delimited content (including delimiters if present)
      /// - `content`: The parsed content between delimiters
      ///
      /// # Examples
      ///
      /// ```ignore
      #[doc = concat!("let delimited = ", stringify!($name), "::new(span, content);")]
      /// ```
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn new(span: Span, content: Content) -> Self {
        Self {
          span,
          content,
          _m: PhantomData,
        }
      }

      /// Returns the span of the entire delimited content.
      ///
      /// This includes the delimiters if they were present during parsing.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn span(&self) -> Span {
        self.span
      }

      /// Returns a mutable reference to the span.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn span_mut(&mut self) -> &mut Span {
        &mut self.span
      }

      /// Returns a reference to the content between the delimiters.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn content(&self) -> &Content {
        &self.content
      }

      /// Consumes self and returns the span and the content between the delimiters.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub fn into_parts(self) -> (Span, Content) {
        (self.span, self.content)
      }

      #[doc = concat!("Returns a parser that expects content delimited by `", $delim_open, "` and `", $delim_close, "`.")]
      ///
      /// This is a **strict parser** that fails if either delimiter is missing.
      /// For error recovery, use [`recoverable_parser`](Self::recoverable_parser) instead.
      ///
      /// # Parameters
      ///
      /// - `content_parser`: Parser for the content between delimiters
      ///
      /// # Examples
      ///
      /// ```ignore
      #[doc = concat!("let parser = ", stringify!($name), "::parser(my_content_parser);")]
      /// ```
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub fn parser<'a, I, T, Error, E>(
        content_parser: impl Parser<'a, I, Content, E> + Clone,
      ) -> impl Parser<'a, I, Self, E> + Clone
      where
        T: PunctuatorToken<'a>,
        str: Equivalent<T>,
        Lang: Language,
        Lang::SyntaxKind: From<$left_type> + From<$right_type> + 'a,
        Error: From<UnexpectedToken<'a, T, Lang::SyntaxKind>>
          + From<<T::Logos as Logos<'a>>::Error>
          + 'a,
        Self: Sized + 'a,
        I: LogoStream<'a, T, Slice = <<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
        T: Token<'a>,
        E: ParserExtra<'a, I, Error = Error> + 'a,
      {
        content_parser
          .delimited_by(
            $open_fn(|| $left_type.into()),
            $close_fn(|| $right_type.into()),
          )
          .map_with(|content, exa| Self::new(exa.span(), content))
      }

      #[doc = concat!("Returns a recoverable parser for content delimited by `", $delim_open, "` and `", $delim_close, "`.")]
      ///
      /// This parser implements comprehensive error recovery for delimiter errors while
      /// delegating content-level recovery to the provided content parser. It handles
      /// three distinct recovery scenarios based on delimiter presence.
      ///
      /// # Recovery Strategy
      ///
      /// This parser follows a **two-tier recovery** philosophy:
      #[doc = concat!("- **Delimiter level**: Handle ", $delim_open, "/", $delim_close, " presence/absence (structural errors)")]
      /// - **Content level**: The `content_parser` handles content-specific errors
      /// - **Separation of concerns**: Each parser layer handles its own recovery boundaries
      ///
      #[doc = concat!("## Scenario 1: Has Opening Delimiter `", $delim_open, "`")]
      ///
      #[doc = concat!("**Input**: `", $delim_open, " content` (missing closing delimiter) or `", $delim_open, " content ", $delim_close, "`")]
      ///
      /// **Behavior**:
      /// - Parse content normally
      /// - Closing delimiter is **optional** (`.or_not()`)
      #[doc = concat!("- If missing: Emit `", stringify!($unclosed_error), "` error with span of entire delimited region")]
      #[doc = concat!("- Return `", stringify!($name), "` with all successfully parsed content")]
      ///
      #[doc = concat!("## Scenario 2: No Opening Delimiter, Has Closing Delimiter `", $delim_close, "`")]
      ///
      #[doc = concat!("**Input**: `content ", $delim_close, "` (missing opening delimiter)")]
      ///
      /// **Behavior**:
      /// - Use `skip_through_closing_delimiter` to scan for closing delimiter
      #[doc = concat!("- If found: Rewind and emit `", stringify!($unopened_error), "` error")]
      /// - Parse content from start to closing delimiter
      #[doc = concat!("- Return `", stringify!($name), "` with recovered content")]
      ///
      /// ## Scenario 3: Neither Opening Nor Closing Delimiter
      ///
      /// **Input**: `content` (no delimiters at all)
      ///
      /// **Behavior**:
      #[doc = concat!("- Emit `", stringify!($undelimited_error), "` error with span from start to EOF")]
      /// - Parse all remaining content (until EOF or outer delimiter)
      #[doc = concat!("- Return `", stringify!($name), "` with all parsed content")]
      ///
      /// # Error Emission
      ///
      #[doc = concat!("- **Delimiter errors**: Emitted by this parser (", stringify!($unclosed_error), ", ", stringify!($unopened_error), ", ", stringify!($undelimited_error), ")")]
      /// - **Content errors**: Emitted by the `content_parser` (not this parser's concern)
      /// - **Lexer errors**: Automatically propagated through error emitter
      ///
      /// # Examples
      ///
      /// ## Well-Formed
      ///
      /// ```text
      #[doc = concat!("Input:  ", $delim_open, " item1 item2 item3 ", $delim_close)]
      /// Errors: (none)
      #[doc = concat!("Result: ", stringify!($name), " with 3 items")]
      /// ```
      ///
      /// ## Missing Closing Delimiter
      ///
      /// ```text
      #[doc = concat!("Input:  ", $delim_open, " item1 item2 item3")]
      #[doc = concat!("Errors: ", stringify!($unclosed_error), " at position of entire region")]
      #[doc = concat!("Result: ", stringify!($name), " with 3 items")]
      /// ```
      ///
      /// ## Missing Opening Delimiter
      ///
      /// ```text
      #[doc = concat!("Input:  item1 item2 item3 ", $delim_close)]
      #[doc = concat!("Errors: ", stringify!($unopened_error), " at position of content + closing delimiter")]
      #[doc = concat!("Result: ", stringify!($name), " with 3 items")]
      /// ```
      ///
      /// ## Missing Both Delimiters
      ///
      /// ```text
      /// Input:  item1 item2 item3
      #[doc = concat!("Errors: ", stringify!($undelimited_error), " at position of entire content")]
      #[doc = concat!("Result: ", stringify!($name), " with 3 items")]
      /// ```
      ///
      /// ## With Malformed Content
      ///
      /// ```text
      #[doc = concat!("Input:  ", $delim_open, " good_item BAD!@# good_item ", $delim_close)]
      /// Errors: (content parser emits error for BAD!@#)
      #[doc = concat!("Result: ", stringify!($name), " with good_item, error_node, good_item")]
      /// ```
      ///
      /// # Design Rationale
      ///
      /// This two-tier approach (delimiter-level + content-level recovery) matches
      /// production compilers like:
      /// - **rustc/rust-analyzer**: Block recovery vs statement recovery
      /// - **TypeScript**: Block synchronization vs statement error tolerance
      /// - **Swift**: Delimiter matching vs expression recovery
      ///
      /// The key insight is that **delimiter errors are structural** (delimiter-level concern)
      /// while **syntax errors are local** (content-level concern).
      pub fn recoverable_parser<'a, I, T, Error, E>(
        content_parser: impl Parser<'a, I, Content, E> + Clone,
      ) -> impl Parser<'a, I, Self, E> + Clone
      where
        T: PunctuatorToken<'a>,
        str: Equivalent<T>,
        Lang: Language,
        Lang::SyntaxKind: From<$left_type> + From<$right_type> + 'a,
        Error: From<UnexpectedToken<'a, T, Lang::SyntaxKind>>
          + From<$unclosed_error>
          + From<$undelimited_error>
          + From<$unopened_error>
          + From<UnexpectedEot>
          + From<<T::Logos as Logos<'a>>::Error>
          + 'a,
        Self: Sized + 'a,
        I: LogoStream<'a, T, Slice = <<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
        T: Token<'a>,
        E: ParserExtra<'a, I, Error = Error> + 'a,
      {
        custom(move |inp| {
          let before = inp.cursor();

          // ============================================================
          // STEP 1: Check for opening delimiter
          // ============================================================
          let tok: Option<Lexed<'_, T>> = inp.peek();
          let open_delimiter_token = match tok {
            // Empty input: cannot parse delimited content at all
            None => return Err(Error::from(UnexpectedEot::eot(inp.span_since(&before)))),
            Some(Lexed::Token(t)) if t.$check_open_fn() => {
              inp.skip(); // Consume the opening delimiter
              true
            }
            // Other token: might still be valid content (without opening delimiter)
            _ => false,
          };

          // ============================================================
          // SCENARIO 1: Has opening delimiter
          // ============================================================
          if open_delimiter_token {
            // Parse content until closing delimiter (or EOF if missing)
            let content = inp.parse(
              content_parser.clone().then_ignore(
                $close_fn(|| $right_type.into())
                  .or_not() // Make closing delimiter optional for recovery
                  .validate(|t, exa, emitter| {
                    if t.is_none() {
                      // Closing delimiter is missing - emit error
                      emitter.emit(Error::from($unclosed_error::$delim_method(exa.span())));
                    }
                    t
                  }),
              ),
            )?;
            return Ok(Self::new(inp.span_since(&before), content));
          }

          // ============================================================
          // STEP 2: No opening delimiter - scan for closing delimiter
          // ============================================================
          let checkpoint = inp.save();

          // Scan ahead to see if there's a closing delimiter anywhere
          let (scaned, closing_delim) =
            inp.parse(skip_through_closing_delimiter(Delimiter::$delim_enum))?;

          // ============================================================
          // SCENARIO 2: No opening delimiter, but has closing delimiter
          // ============================================================
          if closing_delim.is_some() {
            inp.rewind(checkpoint); // Rewind to parse content properly
            // Emit unopened delimiter error (use scaned span from start to closing delimiter)
            let _ = inp.parse(emit_with(move || {
              Error::from($unopened_error::$delim_method(scaned))
            }));

            // Parse content from start up to the closing delimiter
            let content = inp.parse(
              content_parser
                .clone()
                .then_ignore($close_fn(|| $right_type.into())),
            )?;
            return Ok(Self::new(inp.span_since(&before), content));
          }

          // ============================================================
          // SCENARIO 3: Neither opening nor closing delimiter
          // ============================================================
          inp.rewind(checkpoint); // Rewind to parse all content
          // Emit undelimited error (use scaned span from start to EOF)
          let _ = inp.parse(emit_with(move || {
            Error::from($undelimited_error::$delim_method(scaned))
          }));

          // Parse all remaining content (until EOF or outer delimiter)
          // The content parser handles its own recovery for malformed content
          let content = inp.parse(content_parser.clone())?;

          Ok(Self::new(inp.span_since(&before), content))
        })
      }
    }
  };
}

// Generate all four delimiter types using the macro
delimited_by! {
  /// Content delimited by braces `{` and `}`.
  ///
  /// This type provides both strict and recoverable parsing for content enclosed
  /// by brace delimiters. It's commonly used for:
  /// - Block statements in programming languages
  /// - Object literals in JSON-like formats
  /// - Compound expressions
  /// - Scope definitions
  ///
  /// # Examples
  ///
  /// ```ignore
  /// // Parse a block of statements
  /// let parser = DelimitedByBrace::recoverable_parser(statement_parser);
  /// ```
  DelimitedByBrace {
    delimiter_name: "brace",
    delimiter_open: "{",
    delimiter_close: "}",
    delimiter_enum: Brace,
    delimiter_method: brace,
    left_delim_type: LBrace,
    right_delim_type: RBrace,
    open_fn: brace_open,
    close_fn: brace_close,
    check_open_fn: is_brace_open,
    unclosed_error: UnclosedBrace,
    unopened_error: UnopenedBrace,
    undelimited_error: UndelimitedBrace,
  }
}

delimited_by! {
  /// Content delimited by parentheses `(` and `)`.
  ///
  /// This type provides both strict and recoverable parsing for content enclosed
  /// by parenthesis delimiters. It's commonly used for:
  /// - Function call arguments
  /// - Grouped expressions
  /// - Tuple definitions
  /// - Parameter lists
  ///
  /// # Examples
  ///
  /// ```ignore
  /// // Parse function arguments
  /// let parser = DelimitedByParen::recoverable_parser(argument_list_parser);
  /// ```
  DelimitedByParen {
    delimiter_name: "paren",
    delimiter_open: "(",
    delimiter_close: ")",
    delimiter_enum: Paren,
    delimiter_method: paren,
    left_delim_type: LParen,
    right_delim_type: RParen,
    open_fn: paren_open,
    close_fn: paren_close,
    check_open_fn: is_paren_open,
    unclosed_error: UnclosedParen,
    unopened_error: UnopenedParen,
    undelimited_error: UndelimitedParen,
  }
}

delimited_by! {
  /// Content delimited by brackets `[` and `]`.
  ///
  /// This type provides both strict and recoverable parsing for content enclosed
  /// by bracket delimiters. It's commonly used for:
  /// - Array literals
  /// - Index expressions
  /// - Attribute annotations
  /// - List comprehensions
  ///
  /// # Examples
  ///
  /// ```ignore
  /// // Parse an array literal
  /// let parser = DelimitedByBracket::recoverable_parser(element_list_parser);
  /// ```
  DelimitedByBracket {
    delimiter_name: "bracket",
    delimiter_open: "[",
    delimiter_close: "]",
    delimiter_enum: Bracket,
    delimiter_method: bracket,
    left_delim_type: LBracket,
    right_delim_type: RBracket,
    open_fn: bracket_open,
    close_fn: bracket_close,
    check_open_fn: is_bracket_open,
    unclosed_error: UnclosedBracket,
    unopened_error: UnopenedBracket,
    undelimited_error: UndelimitedBracket,
  }
}

delimited_by! {
  /// Content delimited by angle brackets `<` and `>`.
  ///
  /// This type provides both strict and recoverable parsing for content enclosed
  /// by angle bracket delimiters. It's commonly used for:
  /// - Generic type parameters
  /// - Template arguments
  /// - XML/HTML tags
  /// - Comparison chains (with careful context handling)
  ///
  /// # Examples
  ///
  /// ```ignore
  /// // Parse generic type parameters
  /// let parser = DelimitedByAngle::recoverable_parser(type_param_list_parser);
  /// ```
  DelimitedByAngle {
    delimiter_name: "angle",
    delimiter_open: "<",
    delimiter_close: ">",
    delimiter_enum: Angle,
    delimiter_method: angle,
    left_delim_type: LAngle,
    right_delim_type: RAngle,
    open_fn: angle_open,
    close_fn: angle_close,
    check_open_fn: is_angle_open,
    unclosed_error: UnclosedAngle,
    unopened_error: UnopenedAngle,
    undelimited_error: UndelimitedAngle,
  }
}
