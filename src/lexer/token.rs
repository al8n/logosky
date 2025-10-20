use derive_more::{IsVariant, TryUnwrap, Unwrap};
use logos::Lexer;

use crate::utils::{Span, Spanned};

#[cfg(feature = "chumsky")]
use crate::Tokenizer;

pub use logos::Logos;

/// The result of lexing a single token: either a successful token or an error.
///
/// `Lexed` represents the output of the lexing process for a single position in the input.
/// It can either be a successfully recognized [`Token`] with its span information, or a
/// lexing error that occurred at that position.
///
/// # Error Handling Strategy
///
/// `Lexed` enables **error recovery** during lexing by keeping errors in the token stream
/// rather than immediately aborting. This allows you to:
///
/// - Continue lexing after an error to find multiple issues in one pass
/// - Collect all lexing errors before reporting them to the user
/// - Implement "best-effort" parsing that tolerates some malformed input
/// - Provide better diagnostics by showing multiple errors at once
///
/// # Convenience Methods
///
/// Thanks to the `derive_more` macros, `Lexed` provides several utility methods:
///
/// - `is_token()` / `is_error()`: Check which variant this is
/// - `unwrap_token()` / `unwrap_error()`: Unwrap to get the inner value (panics if wrong variant)
/// - `try_unwrap_token()` / `try_unwrap_error()`: Safe unwrapping that returns `Option`
/// - `unwrap_token_ref()` / `unwrap_error_ref()`: Get a reference to the inner value
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust,ignore
/// use logosky::{Lexed, TokenExt};
///
/// let mut lexer = logos::Lexer::<MyTokens>::new(input);
///
/// while let Some(lexed) = MyToken::lex(&mut lexer) {
///     match lexed {
///         Lexed::Token(spanned_token) => {
///             println!("Token: {:?} at {:?}", spanned_token.data(), spanned_token.span());
///         }
///         Lexed::Error(err) => {
///             eprintln!("Lexing error: {:?}", err);
///         }
///     }
/// }
/// ```
///
/// ## Error Collection
///
/// ```rust,ignore
/// let mut tokens = Vec::new();
/// let mut errors = Vec::new();
///
/// let mut lexer = logos::Lexer::<MyTokens>::new(input);
/// while let Some(lexed) = MyToken::lex(&mut lexer) {
///     match lexed {
///         Lexed::Token(tok) => tokens.push(tok),
///         Lexed::Error(err) => errors.push(err),
///     }
/// }
///
/// if !errors.is_empty() {
///     report_lexing_errors(&errors);
/// }
/// ```
///
/// ## Using Convenience Methods
///
/// ```rust,ignore
/// if lexed.is_token() {
///     let token = lexed.unwrap_token_ref();
///     process_token(token);
/// }
///
/// // Safe unwrapping
/// if let Some(token) = lexed.try_unwrap_token() {
///     use_token(token);
/// }
/// ```
#[derive(Debug, PartialEq, IsVariant, Unwrap, TryUnwrap)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum Lexed<'a, T: Token<'a>> {
  /// A successfully recognized token with its span information.
  ///
  /// The token is wrapped in a [`Spanned`] that contains both the token data
  /// and its location in the source input.
  Token(Spanned<T>),

  /// A lexing error that occurred during tokenization.
  ///
  /// The error type is determined by the Logos lexer's error type. It typically
  /// contains information about what went wrong and where in the input it occurred.
  Error(<T::Logos as Logos<'a>>::Error),
}

impl<'a, T> Clone for Lexed<'a, T>
where
  T: Token<'a>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    match self {
      Self::Token(tok) => Self::Token(tok.clone()),
      Self::Error(err) => Self::Error(err.clone()),
    }
  }
}

impl<'a, T> Copy for Lexed<'a, T>
where
  T: Token<'a> + Copy,
  <T::Logos as Logos<'a>>::Error: Copy,
{
}

impl<'a, T: Token<'a>> Lexed<'a, T> {
  /// Lexes the next token from the given lexer, returning `None` if the input is exhausted.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn lex(lexer: &mut Lexer<'a, T::Logos>) -> Option<Self> {
    lexer.next().map(|res| {
      let span = lexer.span();
      res
        .map(|tok| (crate::utils::Span::from(span), T::from(tok)))
        .into()
    })
  }
}

impl<'a, T: 'a> core::fmt::Display for Lexed<'a, T>
where
  T: Token<'a> + core::fmt::Display,
  <T::Logos as Logos<'a>>::Error: core::fmt::Display,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::Token(tok) => ::core::fmt::Display::fmt(tok, f),
      Self::Error(err) => err.fmt(f),
    }
  }
}

impl<'a, T: Token<'a>> From<Result<(Span, T), <T::Logos as Logos<'a>>::Error>> for Lexed<'a, T> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from(value: Result<(Span, T), <T::Logos as Logos<'a>>::Error>) -> Self {
    match value {
      Ok((span, tok)) => Self::Token(Spanned::new(span, tok)),
      Err(err) => Self::Error(err),
    }
  }
}

impl<'a, T: Token<'a>> From<Lexed<'a, T>> for Result<T, <T::Logos as Logos<'a>>::Error> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from(value: Lexed<'a, T>) -> Self {
    match value {
      Lexed::Token(tok) => Ok(tok.into_data()),
      Lexed::Error(err) => Err(err),
    }
  }
}

/// The core trait for token types used with LogoSky.
///
/// `Token` defines the interface that all token types must implement to work with
/// LogoSky's [`Tokenizer`] and Chumsky parsers. It bridges the gap between Logos'
/// lexical analysis and the structured token representation needed for parsing.
///
/// # Design
///
/// The `Token` trait separates the Logos enum (the raw lexer output) from the structured
/// token type that's used in parsing. This separation allows you to:
///
/// - Add custom data or behavior to tokens beyond what Logos provides
/// - Normalize different Logos variants into a unified token type
/// - Implement additional traits and methods specific to your language
/// - Keep parsing logic separate from lexing logic
///
/// # Required Associated Types
///
/// - **`Char`**: The character type used by the lexer (typically `char` for UTF-8 or `u8` for bytes)
/// - **`Kind`**: An enum representing token categories (e.g., `Identifier`, `Number`, `Plus`)
/// - **`Logos`**: The Logos enum that this token type wraps
///
/// # Required Traits
///
/// Implementors must also implement:
/// - `Clone`: Tokens need to be cloneable for backtracking in parsers
/// - `Debug`: For debugging and error messages
/// - `From<Self::Logos>`: Convert from the raw Logos token to the structured token
///
/// # Examples
///
/// ## Basic Implementation
///
/// ```rust,ignore
/// use logosky::Token;
/// use logos::Logos;
///
/// // The Logos enum (raw lexer output)
/// #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
/// enum MyTokens {
///     #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
///     Identifier,
///
///     #[regex(r"[0-9]+")]
///     Number,
///
///     #[token("+")]
///     Plus,
/// }
///
/// // Token kinds (semantic categories)
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// enum TokenKind {
///     Identifier,
///     Number,
///     Plus,
/// }
///
/// // The structured token type
/// #[derive(Debug, Clone, PartialEq)]
/// struct MyToken {
///     kind: TokenKind,
///     // You can add extra fields here
///     // text: String,
///     // value: Option<i64>,
/// }
///
/// impl Token<'_> for MyToken {
///     type Char = char;
///     type Kind = TokenKind;
///     type Logos = MyTokens;
///
///     fn kind(&self) -> Self::Kind {
///         self.kind
///     }
/// }
///
/// impl From<MyTokens> for MyToken {
///     fn from(logos: MyTokens) -> Self {
///         let kind = match logos {
///             MyTokens::Identifier => TokenKind::Identifier,
///             MyTokens::Number => TokenKind::Number,
///             MyTokens::Plus => TokenKind::Plus,
///         };
///         MyToken { kind }
///     }
/// }
/// ```
///
/// ## Advanced: Storing Token Data
///
/// ```rust,ignore
/// // Token that stores the matched text
/// #[derive(Debug, Clone, PartialEq)]
/// struct RichToken<'a> {
///     kind: TokenKind,
///     text: &'a str,
/// }
///
/// impl<'a> Token<'a> for RichToken<'a> {
///     type Char = char;
///     type Kind = TokenKind;
///     type Logos = MyTokens;
///
///     fn kind(&self) -> Self::Kind {
///         self.kind
///     }
/// }
///
/// // Note: From<Logos> implementation would need access to the lexer
/// // to get the matched text, which typically happens in the Tokenizer
/// ```
///
/// ## Working with Bytes
///
/// ```rust,ignore
/// use logosky::Token;
/// use logos::Logos;
///
/// #[derive(Logos, Debug, Clone, Copy)]
/// #[logos(source = [u8])]
/// enum ByteTokens {
///     #[regex(br"[0-9]+")]
///     Number,
/// }
///
/// #[derive(Debug, Clone)]
/// struct ByteToken {
///     kind: ByteTokenKind,
/// }
///
/// impl Token<'_> for ByteToken {
///     type Char = u8;  // Using u8 for byte-based lexing
///     type Kind = ByteTokenKind;
///     type Logos = ByteTokens;
///
///     fn kind(&self) -> Self::Kind {
///         self.kind
///     }
/// }
/// ```
pub trait Token<'a>: Clone + core::fmt::Debug + From<Self::Logos> + 'a {
  /// The character type used by the lexer.
  ///
  /// - Use `char` for text-based lexers processing UTF-8 strings
  /// - Use `u8` for byte-based lexers processing binary data or non-UTF-8 input
  ///
  /// This type must match the character type used by the Logos lexer's source.
  type Char: Copy + core::fmt::Debug + PartialEq + Eq + core::hash::Hash;

  /// The token kind discriminant used to categorize tokens.
  ///
  /// This is typically an enum that represents the semantic category of each token
  /// (e.g., `Identifier`, `Number`, `Operator`). It's separate from the Logos enum
  /// to allow for additional processing or normalization.
  ///
  /// # Requirements
  ///
  /// - Must be `Copy` for efficient passing
  /// - Must be `Debug` for error messages
  /// - Must be `PartialEq` and `Eq` for comparisons in parsers
  /// - Must be `Hash` for use in hash-based collections
  type Kind: Copy + core::fmt::Debug + PartialEq + Eq + core::hash::Hash;

  /// The Logos enum that this token type wraps.
  ///
  /// This is the raw output from the Logos lexer. The `From<Self::Logos>` trait
  /// implementation converts from this type to the structured `Token` type.
  type Logos: Logos<'a> + Clone;

  /// Returns the kind (category) of this token.
  ///
  /// This method is used extensively by parsers to determine what kind of token
  /// they're looking at without having to inspect the full token structure.
  ///
  /// # Example
  ///
  /// ```rust,ignore
  /// let token = MyToken::from(logos_token);
  /// match token.kind() {
  ///     TokenKind::Identifier => handle_identifier(token),
  ///     TokenKind::Number => handle_number(token),
  ///     _ => handle_other(token),
  /// }
  /// ```
  fn kind(&self) -> Self::Kind;
}

/// A token trait for tokens that preserve all source information during lexing, including trivia.
///
/// This trait extends [`Token`] to support "lossless" lexing, where formatting information
/// like whitespace and comments (collectively called "trivia") is preserved alongside
/// semantic tokens. This is essential for tools that need to:
///
/// - **Format or pretty-print code** while preserving original formatting
/// - **Implement linters** that analyze comments or whitespace
/// - **Build language servers** that provide accurate code navigation
/// - **Create refactoring tools** that maintain code style
///
/// # Trivia Tokens
///
/// Trivia tokens are lexical elements that don't affect the semantic meaning of the code
/// but are important for formatting and presentation. Common examples include:
///
/// - Whitespace (spaces, tabs, newlines)
/// - Comments (line comments, block comments, doc comments)
/// - Formatting tokens specific to your language
///
/// # Working with Trivia
///
/// The [`Tokenizer`](crate::Tokenizer) trait provides utilities for handling trivia:
///
/// - [`skip_trivias()`](crate::Tokenizer::skip_trivias) - Skip over trivia tokens during parsing
/// - [`collect_trivias()`](crate::Tokenizer::collect_trivias) - Collect trivia into a container
///
/// # Example
///
/// ```rust
/// use logosky::{Token, LosslessToken};
/// use logos::Logos;
///
/// #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
/// enum MyTokens {
///     #[regex(r"[ \t\n\r]+")]
///     Whitespace,
///     #[regex(r"//[^\n]*")]
///     LineComment,
///     #[regex(r"/\*([^*]|\*[^/])*\*/")]
///     BlockComment,
///     #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
///     Identifier,
///     #[regex(r"[0-9]+")]
///     Number,
/// }
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// enum MyTokenKind {
///     Whitespace,
///     LineComment,
///     BlockComment,
///     Identifier,
///     Number,
/// }
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct MyToken {
///     kind: MyTokenKind,
/// }
///
/// impl Token<'_> for MyToken {
///     type Char = char;
///     type Kind = MyTokenKind;
///     type Logos = MyTokens;
///
///     fn kind(&self) -> Self::Kind {
///         self.kind
///     }
/// }
///
/// impl From<MyTokens> for MyToken {
///     fn from(logos: MyTokens) -> Self {
///         let kind = match logos {
///             MyTokens::Whitespace => MyTokenKind::Whitespace,
///             MyTokens::LineComment => MyTokenKind::LineComment,
///             MyTokens::BlockComment => MyTokenKind::BlockComment,
///             MyTokens::Identifier => MyTokenKind::Identifier,
///             MyTokens::Number => MyTokenKind::Number,
///         };
///         MyToken { kind }
///     }
/// }
///
/// impl LosslessToken<'_> for MyToken {
///     fn is_trivia(&self) -> bool {
///         // Mark whitespace and comments as trivia
///         matches!(
///             self.kind,
///             MyTokenKind::Whitespace
///                 | MyTokenKind::LineComment
///                 | MyTokenKind::BlockComment
///         )
///     }
/// }
/// ```
///
/// # Design Rationale
///
/// Separating [`LosslessToken`] from [`Token`] allows for:
///
/// - **Flexibility**: Not all parsers need to track trivia; simple parsers can use just [`Token`]
/// - **Performance**: Parsers that skip trivia can do so efficiently without allocating
/// - **Type safety**: The type system ensures trivia-handling methods are only available when appropriate
pub trait LosslessToken<'a>: Token<'a> {
  /// Returns `true` if this token represents trivia (whitespace, comments, etc.).
  ///
  /// Trivia tokens are lexical elements that don't affect the semantic meaning of code
  /// but are important for formatting, documentation, and code presentation.
  ///
  /// # Common Trivia Types
  ///
  /// - Whitespace: spaces, tabs, newlines, carriage returns
  /// - Comments: line comments, block comments, documentation comments
  /// - Language-specific formatting tokens
  ///
  /// # Example
  ///
  /// ```rust
  /// use logosky::{Token, LosslessToken};
  /// use logos::Logos;
  ///
  /// #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
  /// enum MyTokens {
  ///     #[regex(r"[ \t\n]+")]
  ///     Whitespace,
  ///     #[regex(r"//[^\n]*")]
  ///     Comment,
  ///     #[regex(r"[0-9]+")]
  ///     Number,
  /// }
  ///
  /// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  /// enum TokenKind {
  ///     Whitespace,
  ///     Comment,
  ///     Number,
  /// }
  ///
  /// #[derive(Debug, Clone, PartialEq)]
  /// struct MyToken {
  ///     kind: TokenKind,
  /// }
  ///
  /// impl Token<'_> for MyToken {
  ///     type Char = char;
  ///     type Kind = TokenKind;
  ///     type Logos = MyTokens;
  ///     fn kind(&self) -> Self::Kind {
  ///         self.kind
  ///     }
  /// }
  ///
  /// impl From<MyTokens> for MyToken {
  ///     fn from(logos: MyTokens) -> Self {
  ///         let kind = match logos {
  ///             MyTokens::Whitespace => TokenKind::Whitespace,
  ///             MyTokens::Comment => TokenKind::Comment,
  ///             MyTokens::Number => TokenKind::Number,
  ///         };
  ///         MyToken { kind }
  ///     }
  /// }
  ///
  /// impl LosslessToken<'_> for MyToken {
  ///     fn is_trivia(&self) -> bool {
  ///         matches!(self.kind, TokenKind::Whitespace | TokenKind::Comment)
  ///     }
  /// }
  /// ```
  fn is_trivia(&self) -> bool;
}

/// The token extension trait.
pub trait TokenExt<'a>: Token<'a> {
  /// Returns a lexer for the token type from the given input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[cfg(feature = "chumsky")]
  #[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
  fn lexer(input: &'a <Self::Logos as Logos<'a>>::Source) -> Tokenizer<'a, Self>
  where
    <Self::Logos as Logos<'a>>::Extras: Default,
  {
    Tokenizer::new(input)
  }

  /// Returns a lexer for the token type from the given input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[cfg(feature = "chumsky")]
  #[cfg_attr(docsrs, doc(cfg(feature = "chumsky")))]
  fn lexer_with_state(
    input: &'a <Self::Logos as Logos<'a>>::Source,
    state: <Self::Logos as Logos<'a>>::Extras,
  ) -> Tokenizer<'a, Self> {
    Tokenizer::with_state(input, state)
  }

  /// Lexes the next token from the given lexer, returning `None` if the input is exhausted.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn lex(lexer: &mut Lexer<'a, Self::Logos>) -> Option<Lexed<'a, Self>> {
    Lexed::lex(lexer)
  }
}

impl<'a, T> TokenExt<'a> for T where T: Token<'a> {}
