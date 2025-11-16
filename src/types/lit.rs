//! Literal token types for language syntax trees.
//!
//! This module provides generic literal types that represent various kinds of
//! literal values found in programming languages: numbers, strings, booleans, etc.
//! Each literal type carries its source representation along with span information.
//!
//! # Design Philosophy
//!
//! All literal types follow the same pattern as [`Ident`](super::Ident):
//!
//! - **Generic string type `S`**: Support `&str`, `String`, or interned strings
//! - **Language marker `Lang`**: Type-safe language distinction
//! - **Span tracking**: All literals carry source location for diagnostics
//! - **Error recovery**: Implement [`ErrorNode`] for placeholder creation
//!
//! # Available Literal Types
//!
//! ## Generic Literal
//!
//! - [`Lit`]: Generic literal (any literal type)
//!
//! ## Numeric Literals
//!
//! - [`LitDecimal`]: Base-10 integer (e.g., `42`, `1_000`)
//! - [`LitHex`]: Hexadecimal integer (e.g., `0xFF`, `0x1A2B`)
//! - [`LitOctal`]: Octal integer (e.g., `0o77`, `0o644`)
//! - [`LitBinary`]: Binary integer (e.g., `0b1010`, `0b1111_0000`)
//! - [`LitFloat`](crate::types::lit::LitFloat): Floating-point (e.g., `3.14`, `1.0e-5`)
//! - [`LitHexFloat`]: Hexadecimal float (e.g., `0x1.8p3`)
//!
//! ## String Literals
//!
//! - [`LitString`]: Single-line string (e.g., `"hello"`)
//! - [`LitMultilineString`]: Multi-line string (e.g., `"""..."""`)
//! - [`LitRawString`]: Raw string without escape processing (e.g., `r"C:\path"`)
//!
//! ## Character/Byte Literals
//!
//! - [`LitChar`]: Character literal (e.g., `'a'`, `'\n'`)
//! - [`LitByte`]: Byte literal (e.g., `b'a'`, `b'\x7F'`)
//! - [`LitByteString`]: Byte string (e.g., `b"bytes"`)
//!
//! ## Boolean and Null
//!
//! - [`LitBool`]: Boolean literal (`true`/`false`)
//! - [`LitNull`]: Null/nil literal
//!
//! # Common Usage Patterns
//!
//! ## Zero-Copy Parsing
//!
//! ```rust,ignore
//! use logosky::types::{Lit, LitDecimal, LitString};
//! use logosky::utils::Span;
//!
//! // Parse literals without allocating
//! type YulLit<'a> = Lit<&'a str, YulLang>;
//! type YulDecimal<'a> = LitDecimal<&'a str, YulLang>;
//! type YulString<'a> = LitString<&'a str, YulLang>;
//!
//! let generic = YulLit::new(Span::new(0, 2), "42");
//! let num = YulDecimal::new(Span::new(0, 2), "42");
//! let str = YulString::new(Span::new(5, 12), "\"hello\"");
//! ```
//!
//! ## Owned Literals
//!
//! ```rust,ignore
//! // Store literals in AST nodes
//! type OwnedDecimal = LitDecimal<String, MyLang>;
//!
//! let lit = OwnedDecimal::new(span, source.to_string());
//! ```
//!
//! # Error Recovery
//!
//! All literal types implement [`ErrorNode`] when `S: ErrorNode`:
//!
//! ```rust,ignore
//! use logosky::types::LitDecimal;
//! use logosky::error::ErrorNode;
//!
//! // Create placeholder for malformed literal
//! let bad_lit = LitDecimal::<String, YulLang>::error(span);
//!
//! // Create placeholder for missing literal
//! let missing_lit = LitDecimal::<String, YulLang>::missing(span);
//! ```

use core::marker::PhantomData;

use crate::{
  error::ErrorNode,
  utils::{AsSpan, IntoComponents, Span},
};

/// A macro to generate literal type structures.
///
/// This reduces boilerplate by generating identical structure and implementations
/// for all literal types.
macro_rules! define_literal {
  (
    $(#[$meta:meta])*
    $name:ident,
    $doc:expr,
    $example_str:expr,
    $example_desc:expr
  ) => {
    paste::paste! {
      $(#[$meta])*
      #[doc = $doc]
      ///
      /// # Type Parameters
      ///
      /// - `S`: The source string type (`&str`, `String`, interned string, etc.)
      /// - `Lang`: Language marker type for type safety
      ///
      /// # Examples
      ///
      /// ## Creating Literals
      ///
      /// ```rust
      #[doc = "use logosky::types::" $name ";"]
      /// use logosky::utils::Span;
      /// # struct MyLang;
      ///
      #[doc = "let lit = " $name "::<&str, MyLang>::new("]
      #[doc = "    Span::new(0, 4),"]
      #[doc = "    " $example_str ]
      /// );
      ///
      #[doc = "assert_eq!(lit.source_ref(), &" $example_str ");"]
      /// ```
      ///
      /// ## With Error Recovery
      ///
      /// ```rust,ignore
      #[doc = "use logosky::types::" $name ";"]
      /// use logosky::error::ErrorNode;
      ///
      #[doc = "// " $example_desc]
      #[doc = "let bad_lit = " $name "::<String, YulLang>::error(span);"]
      /// ```
      #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
      pub struct $name<S, Lang> {
        span: Span,
        source: S,
        _lang: PhantomData<Lang>,
      }
    }

    impl<S, Lang> AsSpan<Span> for $name<S, Lang> {
      #[cfg_attr(not(tarpaulin), inline(always))]
      fn as_span(&self) -> &Span {
        self.span_ref()
      }
    }

    impl<S, Lang> IntoComponents for $name<S, Lang> {
      type Components = (Span, S);

      #[cfg_attr(not(tarpaulin), inline(always))]
      fn into_components(self) -> Self::Components {
        (self.span, self.source)
      }
    }

    impl<S, Lang> $name<S, Lang> {
      /// Creates a new literal with the given span and source string.
      ///
      /// # Parameters
      ///
      /// - `span`: The source location of this literal
      /// - `source`: The literal's source text
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn new(span: Span, source: S) -> Self {
        Self {
          span,
          source,
          _lang: PhantomData,
        }
      }

      /// Returns the span (source location) of this literal.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn span(&self) -> Span {
        self.span
      }

      /// Returns an immutable reference to the span.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn span_ref(&self) -> &Span {
        &self.span
      }

      /// Returns a mutable reference to the span.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn span_mut(&mut self) -> &mut Span {
        &mut self.span
      }

      /// Returns a mutable reference to the source string.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn source_mut(&mut self) -> &mut S {
        &mut self.source
      }

      /// Returns an immutable reference to the source string.
      ///
      /// This is the most common way to access the literal's text.
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn source_ref(&self) -> &S {
        &self.source
      }

      /// Returns a copy of the source string by value.
      ///
      /// Only available when `S` implements [`Copy`].
      #[cfg_attr(not(tarpaulin), inline(always))]
      pub const fn source(self) -> S
      where
        S: Copy,
      {
        self.source
      }
    }

    impl<S, Lang> ErrorNode for $name<S, Lang>
    where
      S: ErrorNode,
    {
      /// Creates a placeholder literal for **malformed content**.
      #[cfg_attr(not(tarpaulin), inline(always))]
      fn error(span: Span) -> Self {
        Self::new(span, S::error(span))
      }

      /// Creates a placeholder literal for **missing required content**.
      #[cfg_attr(not(tarpaulin), inline(always))]
      fn missing(span: Span) -> Self {
        Self::new(span, S::missing(span))
      }
    }
  };
}

// Generic literal
define_literal!(
  /// A generic literal.
  ///
  /// Represents any kind of literal value without distinguishing between specific
  /// types (numeric, string, boolean, etc.). Useful when the exact literal type
  /// doesn't matter for your use case.
  Lit,
  "A generic literal (any literal type).",
  "\"value\"",
  "Malformed literal"
);

// Numeric literals
define_literal!(
  /// A decimal (base-10) integer literal.
  ///
  /// Represents numeric literals in standard decimal notation, such as `42`, `1000`,
  /// or `123_456`. The source string may include underscores for readability but
  /// represents a single integer value.
  LitDecimal,
  "A decimal integer literal (e.g., `42`, `1_000`).",
  "\"42\"",
  "Malformed decimal literal like \"12abc\""
);

define_literal!(
  /// A hexadecimal (base-16) integer literal.
  ///
  /// Represents integer literals in hexadecimal notation, typically prefixed with
  /// `0x` or `0X`, such as `0xFF`, `0x1A2B`, or `0xDEAD_BEEF`.
  LitHex,
  "A hexadecimal integer literal (e.g., `0xFF`, `0x1A2B`).",
  "\"0xFF\"",
  "Malformed hex literal like \"0xGG\""
);

define_literal!(
  /// An octal (base-8) integer literal.
  ///
  /// Represents integer literals in octal notation, typically prefixed with `0o`,
  /// such as `0o77`, `0o644`, or `0o755`.
  LitOctal,
  "An octal integer literal (e.g., `0o77`, `0o644`).",
  "\"0o77\"",
  "Malformed octal literal like \"0o89\""
);

define_literal!(
  /// A binary (base-2) integer literal.
  ///
  /// Represents integer literals in binary notation, typically prefixed with `0b`,
  /// such as `0b1010`, `0b11110000`, or `0b1111_0000`.
  LitBinary,
  "A binary integer literal (e.g., `0b1010`, `0b1111_0000`).",
  "\"0b1010\"",
  "Malformed binary literal like \"0b123\""
);

define_literal!(
  /// A floating-point literal.
  ///
  /// Represents floating-point literals in standard decimal notation with optional
  /// fractional and exponent parts, such as `3.14`, `1.0`, `2.5e-3`, or `6.022e23`.
  LitFloat,
  "A floating-point literal (e.g., `3.14`, `1.0e-5`).",
  "\"3.14\"",
  "Malformed float literal like \"3.14.15\""
);

define_literal!(
  /// A hexadecimal floating-point literal.
  ///
  /// Represents floating-point literals in hexadecimal notation with binary exponent,
  /// such as `0x1.8p3` (which equals 12.0 in decimal). Used in languages like C and Rust
  /// for precise floating-point representation.
  LitHexFloat,
  "A hexadecimal floating-point literal (e.g., `0x1.8p3`).",
  "\"0x1.8p3\"",
  "Malformed hex float like \"0x1.Gp3\""
);

// String literals
define_literal!(
  /// A single-line string literal.
  ///
  /// Represents string literals enclosed in quotes, typically on a single line,
  /// such as `"hello"`, `"world\n"`, or `"escaped \"quotes\""`. May contain
  /// escape sequences.
  LitString,
  "A single-line string literal (e.g., `\"hello\"`, `\"world\\n\"`).",
  "\"\\\"hello\\\"\"",
  "Malformed string like unterminated \"hello"
);

define_literal!(
  /// A multi-line string literal.
  ///
  /// Represents string literals that span multiple lines, often with special delimiters
  /// like triple quotes (`"""..."""` or `'''...'''`). Common in languages like Python,
  /// Kotlin, and Swift.
  LitMultilineString,
  "A multi-line string literal (e.g., `\"\"\"...\"\"\"`).",
  "\"\\\"\\\"\\\"multi\\nline\\\"\\\"\\\"\"",
  "Malformed multiline string"
);

define_literal!(
  /// A raw string literal.
  ///
  /// Represents string literals where escape sequences are not processed, often
  /// prefixed with `r` (e.g., Rust's `r"C:\path"`, Python's `r"\n stays literal"`).
  /// Useful for regular expressions and file paths.
  LitRawString,
  "A raw string literal without escape processing (e.g., `r\"C:\\path\"`).",
  "\"r\\\"C:\\\\path\\\"\"",
  "Malformed raw string"
);

// Character and byte literals
define_literal!(
  /// A character literal.
  ///
  /// Represents a single character enclosed in single quotes, such as `'a'`, `'\\n'`,
  /// or `'\\u{1F600}'`. May contain escape sequences for special characters.
  LitChar,
  "A character literal (e.g., `'a'`, `'\\n'`, `'\\u{1F600}'`).",
  "\"'a'\"",
  "Malformed char like unclosed 'a"
);

define_literal!(
  /// A byte literal.
  ///
  /// Represents a single byte value enclosed in single quotes with a `b` prefix,
  /// such as `b'a'`, `b'\\x7F'`, or `b'\\n'`. Used in languages like Rust for
  /// ASCII/byte manipulation.
  LitByte,
  "A byte literal (e.g., `b'a'`, `b'\\x7F'`).",
  "\"b'a'\"",
  "Malformed byte literal"
);

define_literal!(
  /// A byte string literal.
  ///
  /// Represents a sequence of bytes enclosed in quotes with a `b` prefix, such as
  /// `b"bytes"`, `b"\\x48\\x65\\x6C\\x6C\\x6F"`. Used for binary data or ASCII strings.
  LitByteString,
  "A byte string literal (e.g., `b\"bytes\"`, `b\"\\x48\\x65\\x6C\\x6C\\x6F\"`).",
  "\"b\\\"bytes\\\"\"",
  "Malformed byte string"
);

// Boolean and null
define_literal!(
  /// A boolean literal.
  ///
  /// Represents boolean values `true` or `false`. The source string contains the
  /// actual keyword as it appears in source code.
  LitBool,
  "A boolean literal (`true` or `false`).",
  "\"true\"",
  "Malformed boolean like \"tru\" or \"fals\""
);

define_literal!(
  /// A null/nil literal.
  ///
  /// Represents the null, nil, or None value in various programming languages.
  /// The source string contains the keyword as it appears (e.g., `null`, `nil`,
  /// `None`, `nullptr`).
  LitNull,
  "A null/nil literal (e.g., `null`, `nil`, `None`).",
  "\"null\"",
  "Malformed null literal"
);

// Chumsky parser implementations
#[cfg(feature = "chumsky")]
#[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
const _: () = {
  use chumsky::{Parser, extra::ParserExtra, prelude::*};
  use logos::{Logos, Source};

  use crate::{
    Lexed, LitToken, LogoStream, error::UnexpectedToken, syntax::Language, utils::Spanned,
  };

  /// A macro to generate parser implementations for literal types.
  ///
  /// This generates a consistent parser method for each literal type that validates
  /// the token is the correct literal kind.
  macro_rules! impl_literal_parser {
    ($name:ident, $check_method:ident, $doc_kind:expr, $example_token:expr) => {
      paste::paste! {
        impl<S, Lang> $name<S, Lang> {
          #[doc = concat!("Creates a Chumsky parser that parses ", $doc_kind, " tokens into `", stringify!($name), "`.")]
          ///
          /// This parser validates that the token is the expected literal type
          /// and converts it with proper span tracking.
          ///
          /// # Type Parameters
          ///
          /// - `'a`: Lifetime of the input source
          /// - `I`: Token stream implementing [`LogoStream`]
          /// - `T`: Token type implementing [`LitToken`]
          /// - `Error`: Error type that can be constructed from lexer and parser errors
          /// - `E`: Parser extra state carrying errors and metadata
          ///
          /// # Parameters
          ///
          /// - `lit_kind`: Function that returns the expected syntax kind for error
          ///   reporting. Called when wrong literal type is found.
          /// - `extract`: Function that extracts the literal source from a token.
          ///   Should return `Some(source)` for matching tokens, `None` otherwise.
          ///
          /// # Returns
          ///
          /// A Chumsky parser that produces
          #[doc = "`" $name "<S, Lang>`"]
          /// on success or emits an
          /// [`UnexpectedToken`] error when wrong token type is found.
          ///
          /// # Examples
          ///
          /// ## Basic Usage
          ///
          /// ```rust,ignore
          #[doc = "use logosky::types::" $name ";"]
          /// use logosky::chumsky::Parser;
          ///
          #[doc = "// Parser for " $doc_kind]
          #[doc = "let lit_parser = " $name "::<&str, YulLang>::parser("]
          ///     || YulSyntaxKind::DecimalLit,
          ///     |tok| if let YulToken::DecimalLit(s) = tok { Some(s) } else { None }
          /// );
          ///
          #[doc = "// Parse " $example_token " into " $name]
          /// let result = lit_parser.parse(stream)?;
          /// ```
          ///
          /// ## With Error Recovery
          ///
          /// ```rust,ignore
          #[doc = "use logosky::types::" $name ";"]
          /// use logosky::error::ErrorNode;
          /// use logosky::chumsky::{Parser, prelude::*};
          ///
          /// // Parser with recovery for missing literals
          #[doc = "let lit_parser = " $name "::<String, YulLang>::parser("]
          ///     || YulSyntaxKind::DecimalLit,
          ///     |tok| if let YulToken::DecimalLit(s) = tok { Some(s) } else { None }
          /// ).recover_with(via_parser(
          ///     // Create placeholder on error
          #[doc = "    empty().map_with(|_, exa| " $name "::missing(exa.span()))"]
          /// ));
          /// ```
          #[cfg_attr(not(tarpaulin), inline(always))]
          pub fn parser<'a, I, T, Error, E, F>(
            lit_kind: impl Fn() -> Lang::SyntaxKind + Clone + 'a,
            extract: F,
          ) -> impl Parser<'a, I, Self, E> + Clone + 'a
          where
            I: LogoStream<'a, T>,
            T: LitToken<'a>,
            S: From<<<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>> + 'a,
            Lang: Language,
            Lang::SyntaxKind: 'a,
            F: Fn(&T) -> Option<<<<T>::Logos as Logos<'a>>::Source as Source>::Slice<'a>> + Clone + 'a,
            Error: From<<T::Logos as Logos<'a>>::Error>
              + From<<T::Logos as Logos<'a>>::Error>
              + From<UnexpectedToken<'a, T, Lang::SyntaxKind>>,
            E: ParserExtra<'a, I, Error = Error> + 'a,
          {
            any().try_map(move |tok: Lexed<'_, T>, _| match tok {
              Lexed::Token(Spanned { span, data: tok }) => {
                if let Some(source) = extract(&tok) {
                  Ok($name::new(span, source.into()))
                } else {
                  Err(UnexpectedToken::expected_one_with_found(span, tok, lit_kind()).into())
                }
              }
              Lexed::Error(e) => Err(Error::from(e)),
            })
          }
        }
      }
    };
  }

  // Implement parser for generic literal
  impl_literal_parser!(Lit, is_literal, "any literal", "\"value\"");

  // Implement parsers for all numeric literal types
  impl_literal_parser!(LitDecimal, is_decimal_literal, "decimal integer", "\"42\"");
  impl_literal_parser!(
    LitHex,
    is_hexadecimal_literal,
    "hexadecimal integer",
    "\"0xFF\""
  );
  impl_literal_parser!(LitOctal, is_octal_literal, "octal integer", "\"0o77\"");
  impl_literal_parser!(LitBinary, is_binary_literal, "binary integer", "\"0b1010\"");
  impl_literal_parser!(LitFloat, is_float_literal, "floating-point", "\"3.14\"");
  impl_literal_parser!(
    LitHexFloat,
    is_hex_float_literal,
    "hexadecimal floating-point",
    "\"0x1.8p3\""
  );

  // Implement parsers for string literal types
  impl_literal_parser!(
    LitString,
    is_inline_string_literal,
    "single-line string",
    "\"\\\"hello\\\"\""
  );
  impl_literal_parser!(
    LitMultilineString,
    is_multiline_string_literal,
    "multi-line string",
    "\"\\\"\\\"\\\"text\\\"\\\"\\\"\""
  );
  impl_literal_parser!(
    LitRawString,
    is_raw_string_literal,
    "raw string",
    "\"r\\\"path\\\"\""
  );

  // Implement parsers for character/byte literal types
  impl_literal_parser!(LitChar, is_char_literal, "character", "\"'a'\"");
  impl_literal_parser!(LitByte, is_byte_literal, "byte", "\"b'a'\"");
  impl_literal_parser!(
    LitByteString,
    is_byte_string_literal,
    "byte string",
    "\"b\\\"bytes\\\"\""
  );

  // Implement parsers for boolean and null
  impl_literal_parser!(LitBool, is_boolean_literal, "boolean", "\"true\"");
  impl_literal_parser!(LitNull, is_null_literal, "null", "\"null\"");
};
