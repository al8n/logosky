//! Common types for building language-specific ASTs.
//!
//! This module provides generic, reusable building blocks for creating Abstract
//! Syntax Trees (ASTs) across different programming languages. These types are
//! designed to be language-agnostic while maintaining type safety through generic
//! parameters.
//!
//! # Available Types
//!
//! ## Identifiers
//!
//! - [`Ident`]: Generic identifier with span tracking and language marker
//!
//! ## Generic Literal
//!
//! - [`Lit`]: Generic literal (any literal type)
//!
//! ## Numeric Literals
//!
//! - [`LitDecimal`]: Decimal integer (e.g., `42`, `1_000`)
//! - [`LitHex`]: Hexadecimal integer (e.g., `0xFF`, `0x1A2B`)
//! - [`LitOctal`]: Octal integer (e.g., `0o77`, `0o644`)
//! - [`LitBinary`]: Binary integer (e.g., `0b1010`)
//! - [`LitFloat`]: Floating-point (e.g., `3.14`, `1.0e-5`)
//! - [`LitHexFloat`]: Hexadecimal float (e.g., `0x1.8p3`)
//!
//! ## String Literals
//!
//! - [`LitString`]: Single-line string (e.g., `"hello"`)
//! - [`LitMultilineString`]: Multi-line string (e.g., `"""..."""`)
//! - [`LitRawString`]: Raw string (e.g., `r"C:\path"`)
//!
//! ## Character/Byte Literals
//!
//! - [`LitChar`]: Character literal (e.g., `'a'`)
//! - [`LitByte`]: Byte literal (e.g., `b'a'`)
//! - [`LitByteString`]: Byte string (e.g., `b"bytes"`)
//!
//! ## Boolean and Null
//!
//! - [`LitBool`]: Boolean literal (`true`/`false`)
//! - [`LitNull`]: Null/nil literal
//!
//! # Design Principles
//!
//! All types in this module follow these principles:
//!
//! 1. **Generic over string representation**: Support zero-copy (`&str`), owned
//!    (`String`), and interned strings
//! 2. **Span tracking**: Every node carries its source location for diagnostics
//! 3. **Language safety**: Generic `Lang` parameter prevents mixing ASTs from
//!    different languages
//! 4. **Error recovery**: Implement [`ErrorNode`](crate::error::ErrorNode) when
//!    appropriate for creating placeholders during parsing errors
//!
//! # Example: Building a Simple Expression AST
//!
//! ```rust,ignore
//! use logosky::types::Ident;
//! use logosky::utils::Span;
//!
//! // Define your language marker
//! struct MyLang;
//!
//! // Define expression type using Ident
//! enum Expr<'a> {
//!     Variable(Ident<&'a str, MyLang>),
//!     Number(i64, Span),
//!     Add(Box<Expr<'a>>, Box<Expr<'a>>, Span),
//! }
//!
//! // Create an expression
//! let var = Ident::new(Span::new(0, 1), "x");
//! let expr = Expr::Variable(var);
//! ```

pub use ident::*;
pub use lit::*;

mod ident;
mod lit;
