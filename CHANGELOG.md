# UNRELEASED

# 0.2.0 (October 20th, 2024)

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
