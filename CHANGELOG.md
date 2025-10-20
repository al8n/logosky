# UNRELEASED

# 0.3.0 (October 21st, 2025)

## New Features

- **CST (Concrete Syntax Tree) support**: Added new `cst` module with rowan integration (requires `rowan` feature)
  - `SyntaxTreeBuilder<Lang>`: A builder for constructing syntax trees using rowan's GreenNodeBuilder
  - `Parseable<'a, I, T, Error>` trait: Enables types to be parsed from a tokenizer and produce CST nodes
  - `Node` trait: The main trait for converting untyped `SyntaxNode` to typed CST nodes (zero-cost conversion)
  - `SyntaxNodeChildren<N>` iterator: Iterate over children of a particular CST node type
  - `cast` module: Utility functions for casting and accessing CST nodes
    - `child<N>()`: Get the first child of a specific type
    - `children<N>()`: Get all children of a specific type
    - `token<L>()`: Get a token child with a specific kind
  - `error` module: CST-specific error types
    - `SyntaxNodeMismatch<N>`: Error when expected and actual syntax node kinds don't match

## Dependencies

- **Added**: `rowan = "0.16"` (optional, behind `rowan` feature flag)

## Features

- **New feature flag**: `rowan` - Enables CST support with rowan integration (requires `std` feature)

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
