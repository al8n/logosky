use core::ops::Range;

use derive_more::{From, IsVariant, Unwrap, TryUnwrap};

pub use human_display::*;
pub use positioned_char::*;

mod human_display;
mod positioned_char;

/// A zero-copy description of an *unexpected lexeme* for diagnostics.
///
/// Instead of owning text, this stores either:
/// - a single positioned character (`Char`), or
/// - a byte span into the original source (`Range<usize>`).
///
/// Consumers (e.g. error reporters) can slice the original source with these
/// positions to render messages without allocating.
///
/// ## Representation
///
/// - **`Char`**: A single unexpected Unicode scalar value with its position.
///   Useful when the exact character is known (e.g., an unexpected `@`).
///
/// - **`Span`**: A half-open byte range `[start, end)` into the same source
///   buffer that was lexed/parsed. Prefer this for multi-character lexemes
///   (e.g., invalid numeric suffixes, unterminated sequences).
///
/// ## Semantics & Invariants
///
/// - `Span` indices are **byte offsets** into the original source and must
///   satisfy `start < end`. Treat them as UTF-8 boundaries if you plan to
///   slice a `&str`.
/// - `Char` carries the *single* offending character together with its
///   position (e.g., byte offset) via `PositionedChar<Char>`.
/// - This enum doesn’t own the source; it’s just a pointer/offset description
///   for zero-allocation diagnostics.
///
/// ## When to use which
///
/// - Use **`Char`** when the error is caused by one specific character
///   (e.g., “unexpected character `#`”).
/// - Use **`Span`** when a short sequence is at fault
///   (e.g., “invalid suffix `xasd` after integer literal” or
///   “unterminated string starting here”).
///
/// ## Examples
///
/// Extracting and printing the offending slice from the original input:
///
/// ```rust,ignore
/// fn render_unexpected(src: &str, u: &UnexpectedLexeme<char>) -> String {
///     match u {
///         UnexpectedLexeme::Char(pc) => {
///             // Assuming `PositionedChar` exposes the byte offset and char:
///             let ch = pc.char();
///             let pos = pc.position();
///             format!("unexpected character `{}` at byte {}", ch, pos)
///         }
///         UnexpectedLexeme::Span(range) => {
///             // Safety: `range` should point into `src` on UTF-8 boundaries.
///             let snippet = &src[range.clone()];
///             format!("unexpected input `{snippet}` at bytes {}..{}", range.start, range.end)
///         }
///     }
/// }
/// ```
///
/// Emitting an invalid integer suffix as a span:
///
/// ```rust,ignore
/// // e.g., source: "0123xasd query {}"
/// // after lexing the digits, detect `xasd` as an invalid suffix
/// let start = 4; // byte index where the suffix begins
/// let end   = 8; // byte index after the suffix
/// let unexpected = UnexpectedLexeme::Span(start..end);
/// ```
///
/// ## Notes on Unicode
///
/// - `Char` stores a Unicode scalar value.
/// - `Span` uses **byte** indices. If you need character indices for display,
///   convert carefully (e.g., by walking `src.char_indices()`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, From)]
#[unwrap(ref)]
#[try_unwrap(ref)]
pub enum UnexpectedLexeme<Char> {
  /// A single unexpected character with its position.
  Char(PositionedChar<Char>),

  /// A half-open byte range `[start, end)` into the original source.
  ///
  /// The range must be non-empty (`start < end`) and point into the same
  /// buffer that was tokenized. Prefer UTF-8 boundary indices if you plan to
  /// slice `&str`.
  Span(Range<usize>),
}
