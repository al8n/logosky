# UNRELEASED

# 0.3.0 (October 27th, 2025)

## Breaking Changes

- **Chumsky is now optional**: The `chumsky` dependency is now behind the `chumsky` feature flag (enabled by default with `std` feature)
  - Use `default-features = false` if you only need the lexer functionality
  - Renamed `parseable.rs` → `chumsky.rs` to better reflect the optional nature

## New Features

### No-alloc Support

- **Zero-allocation mode**: LogoSky now supports `no_std` + `no_alloc` environments
  - Core lexer and utility types work without heap allocation
  - `alloc` feature enables collection-based utilities
  - `std` feature enables full error handling and format support

### Macros for Token Types

- **`keyword!` macro**: Define keyword tokens with zero boilerplate
  ```rust
  keyword! {
    (Let, "LET", "let"),
    (Const, "CONST", "const"),
  }
  ```
  - Automatically implements common traits (`Debug`, `Clone`, `PartialEq`, etc.)
  - Generic over span type `S` and optional content `C`
  - Provides `AsRef<str>` and `Borrow<str>` implementations

- **`punctuator!` macro**: Define punctuation tokens with minimal code
  ```rust
  punctuator! {
    (LParen, "L_PAREN", "("),
    (RParen, "R_PAREN", ")"),
  }
  ```
  - Similar ergonomics to `keyword!` macro
  - Includes methods for accessing raw string literals

### CST (Concrete Syntax Tree) Support

- **CST module**: Added new `cst` module with rowan integration (requires `rowan` feature)
  - `SyntaxTreeBuilder<Lang>`: A builder for constructing syntax trees using rowan's GreenNodeBuilder
  - `Parseable<'a, I, T, Error>` trait: Enables types to be parsed from a tokenizer and produce CST nodes
  - `CstElement`: Base trait for all typed CST elements (nodes and tokens)
  - `CstNode`: Trait for typed CST nodes with zero-cost conversions from untyped `SyntaxNode`
  - `CstToken`: Trait for typed CST tokens (terminal elements)
  - `SyntaxNodeChildren<N>` iterator: Iterate over children of a particular CST node type

- **CST cast utilities** (in `cst::cast` module):
  - `child<N>()`: Get the first child of a specific type
  - `children<N>()`: Get all children of a specific type
  - `token<L>()`: Get a token child with a specific kind
  - Type-safe casting with proper error handling

- **CST error types** (in `cst::error` module):
  - `Incomplete`: Error for incomplete CST constructions
  - `CstNodeMismatch`: Type mismatch for CST nodes
  - `CstTokenMismatch`: Type mismatch for CST tokens
  - All error types include rich context for better diagnostics

### New Utility Types

- **`Lexeme<Char>`**: Zero-copy description of a lexeme in source code
  - Represents either a single positioned character or a byte span
  - Designed for error reporting without string allocation
  - Provides `is_char()`, `is_span()`, `unwrap_char()`, `unwrap_span()` helpers

- **`UnknownLexeme<Char, Knowledge>`**: Error structure for unrecognized lexemes
  - Pairs an unrecognized lexeme with diagnostic knowledge
  - Generic `Knowledge` parameter allows custom diagnostic types
  - Implements `Deref` to `Lexeme` for convenient access
  - Methods: `from_char()`, `from_span()`, `map_char()`, `map_hint()`, etc.

- **`UnexpectedSuffix<Char>`**: Error for unexpected suffixes after valid tokens
  - Tracks the valid token span and the unexpected suffix
  - Useful for catching errors like `123abc` (invalid number literal)

- **`Unclosed<Delimiter>`**: Error for unclosed delimiters
  - Tracks the opening delimiter position
  - Generic over delimiter type (char, string, custom enum, etc.)

- **`RecursionLimiter`**: Stack overflow protection for recursive parsing
  - Configurable recursion depth limit
  - Returns `RecursionLimitExceeded` error when limit is reached
  - Integrates with logos lexer via `State` trait

- **`TokenTracker` / `TokenLimiter`**: Track the count of tokens yielded and enforce limits
  - `TokenTracker`: Trait for tracking token counts during lexing/parsing
  - `TokenLimiter`: Implementation that prevents DoS attacks by limiting total token count
  - Configurable token limit with `TokenLimitExceeded` error
  - Can be embedded in lexer state via `Extras`
  - Useful for protecting against maliciously large or deeply nested inputs

### Internal Improvements

- **Module restructuring**:
  - Split `lexer.rs` into `lexer/tokenizer.rs` for better organization
  - Moved tokenizer iterator to `lexer/tokenizer/iter.rs`

- **Enhanced `PositionedChar`**:
  - Added more utility methods for character manipulation

- **Improved `Tracker` utilities**:
  - Enhanced position tracking capabilities
  - Better integration with lexer state

## Dependencies

### Added

- **`paste = "1"`**: For macro metaprogramming (required for `keyword!` and `punctuator!` macros)
- **`rowan = "0.16"`** (optional, behind `rowan` feature flag): For CST support
- **`generic-array = "1"`** (optional, with `rowan` feature): For fixed-size arrays in CST operations

### Changed

- **`chumsky`**: Now optional, enabled by `chumsky` feature (enabled by default with `std`)

## Features

- **New feature flag**: `chumsky` - Enables parser combinator support (enabled by default with `std` feature)
- **New feature flag**: `rowan` - Enables CST support with rowan integration (requires `std` and `generic-array`)
- **Modified feature**: `smallvec` - Now requires `alloc` feature

## Bug Fixes

- Fixed formatting issues in documentation
- Improved error message clarity in various utility types
- Better handling of edge cases in lexer position tracking

# 0.2.0 (October 20th, 2025)

## New Features

- **LosslessToken trait**: Introduced `LosslessToken<'a>` trait for tokens that preserve trivia information
  - Provides `is_trivia()` method to identify whitespace, comments, and other non-semantic tokens
  - Enables building parsers that can preserve formatting and comments (important for formatters, linters, and language servers)

- **Trivia handling utilities in Tokenizer**: Added two new parser combinators for working with trivia tokens
  - `skip_trivias<E>()`: Parser that skips over trivia tokens (whitespace, comments, etc.)
    - Useful for parsers that don't need to preserve formatting
    - Returns `()` and consumes trivia tokens from the input stream
  - `collect_trivias<C, E>()`: Parser that collects trivia tokens into a container
    - Useful for formatters, linters, and tools that need to preserve or analyze trivia
    - Generic over any container type implementing `Container<Spanned<T>>`


## Examples

### Using LosslessToken for trivia-aware parsing

```rust
use logosky::{Token, LosslessToken};

#[derive(Debug, Clone, PartialEq)]
struct MyToken {
  kind: MyTokenKind,
}

impl Token<'_> for MyToken {
  type Char = char;
  type Kind = MyTokenKind;
  type Logos = MyTokens;

  fn kind(&self) -> Self::Kind {
    self.kind
  }
}

impl LosslessToken<'_> for MyToken {
  fn is_trivia(&self) -> bool {
    matches!(self.kind, MyTokenKind::Whitespace | MyTokenKind::Comment)
  }
}
```

### Skipping trivia in parsers

```rust
use logosky::Tokenizer;

// Skip all leading trivia before parsing a token
let parser = MyTokenStream::skip_trivias()
  .ignore_then(my_token_parser);
```

### Collecting trivia for formatters

```rust
use logosky::Tokenizer;

// Collect trivia tokens into a Vec
let parser = MyTokenStream::collect_trivias::<Vec<_>, _>()
  .then(my_token_parser);
```
