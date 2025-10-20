use super::*;

/// Iterators for [`Tokenizer`]
pub mod iter;

/// A zero-copy token stream adapter that bridges Logos and Chumsky.
///
/// `Tokenizer` is the core integration layer between [Logos](https://github.com/maciejhirsz/logos)
/// lexical analysis and [Chumsky](https://github.com/zesterer/chumsky) parser combinators.
/// It efficiently wraps a Logos token source and implements all necessary Chumsky input traits,
/// allowing you to use Chumsky parsers directly on Logos tokens.
///
/// # Zero-Copy Design
///
/// `Tokenizer` doesn't allocate or copy tokens. Instead, it maintains a cursor position
/// and calls Logos on-demand as the parser consumes tokens. This makes it efficient for
/// large inputs and streaming scenarios.
///
/// # State Management
///
/// For stateful lexers (those with non-`()` `Extras`), `Tokenizer` maintains the lexer
/// state and passes it through token-by-token. This allows for context-sensitive lexing
/// patterns.
///
/// # Type Parameters
///
/// - `'a`: The lifetime of the input source
/// - `T`: The token type implementing [`Token<'a>`]
///
/// # Implemented Traits
///
/// This type implements all core Chumsky input traits:
/// - [`Input`](chumsky::input::Input) - Basic input stream functionality
/// - [`ValueInput`](chumsky::input::ValueInput) - Token-by-token consumption
/// - [`SliceInput`](chumsky::input::SliceInput) - Slice extraction from source
/// - [`ExactSizeInput`](chumsky::input::ExactSizeInput) - Known input length
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust,ignore
/// use logosky::{Token, Tokenizer, TokenExt};
/// use logos::Logos;
/// use chumsky::prelude::*;
///
/// #[derive(Logos, Debug, Clone, Copy, PartialEq)]
/// #[logos(skip r"[ \t\n]+")]
/// enum MyTokens {
///     #[regex(r"[0-9]+")]
///     Number,
///     #[token("+")]
///     Plus,
/// }
///
/// // Create a token stream from input
/// let input = "42 + 13";
/// let stream = MyToken::lexer(input); // Returns Tokenizer<'_, MyToken>
///
/// // Use with Chumsky parsers
/// let parser = any().repeated().collect::<Vec<_>>();
/// let tokens = parser.parse(stream).into_result();
/// ```
///
/// ## Stateful Lexing
///
/// ```rust,ignore
/// #[derive(Default, Clone)]
/// struct LexerState {
///     brace_count: usize,
/// }
///
/// #[derive(Logos, Debug, Clone, Copy)]
/// #[logos(extras = LexerState)]
/// enum MyTokens {
///     #[token("{", |lex| lex.extras.brace_count += 1)]
///     LBrace,
///     #[token("}", |lex| lex.extras.brace_count -= 1)]
///     RBrace,
/// }
///
/// let input = "{ { } }";
/// let initial_state = LexerState::default();
/// let stream = Tokenizer::with_state(input, initial_state);
/// ```
///
/// ## Cloning and Backtracking
///
/// Tokenizer supports cloning (when the token type and extras are Clone/Copy),
/// which is essential for Chumsky's backtracking:
///
/// ```rust,ignore
/// let stream = MyToken::lexer(input);
/// let checkpoint = stream.clone(); // Save position for backtracking
///
/// // Try to parse something
/// if let Err(_) = try_parser.parse(stream) {
///     // Backtrack by using the cloned stream
///     alternative_parser.parse(checkpoint);
/// }
/// ```
pub struct Tokenizer<'a, T: Token<'a>> {
  pub(crate) input: &'a <T::Logos as Logos<'a>>::Source,
  pub(crate) state: <T::Logos as Logos<'a>>::Extras,
  pub(crate) cursor: usize,
}

impl<'a, T> Clone for Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      input: self.input,
      state: self.state.clone(),
      cursor: self.cursor,
    }
  }
}

impl<'a, T> Copy for Tokenizer<'a, T>
where
  T: Token<'a> + Copy,
  <T::Logos as Logos<'a>>::Extras: Copy,
  <T::Logos as Logos<'a>>::Error: Copy,
{
}

impl<'a, T> core::fmt::Debug for Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("Tokenizer")
      .field("input", &self.input)
      .field("state", &self.state)
      .finish()
  }
}

impl<'a, T> Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Default,
{
  /// Creates a new lexer from the given input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(input: &'a <T::Logos as Logos<'a>>::Source) -> Self {
    Self::with_state(input, <T::Logos as Logos<'a>>::Extras::default())
  }
}

impl<'a, T: Token<'a>> Tokenizer<'a, T> {
  /// Creates a new lexer from the given input and state.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn with_state(
    input: &'a <T::Logos as Logos<'a>>::Source,
    state: <T::Logos as Logos<'a>>::Extras,
  ) -> Self {
    Self {
      input,
      state,
      cursor: 0,
    }
  }
}

impl<'a, T: Token<'a>> Tokenizer<'a, T> {
  /// Returns a reference to the input.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn input(&self) -> &<T::Logos as Logos<'a>>::Source {
    self.input
  }

  /// Returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn iter(&mut self) -> iter::Iter<'a, '_, T> {
    iter::Iter::new(self)
  }

  /// Consumes the lexer and returns an iterator over the tokens of the lexer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn into_iter(self) -> iter::IntoIter<'a, T> {
    iter::IntoIter::new(self)
  }
}
