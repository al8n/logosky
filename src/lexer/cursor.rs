use super::{Lexer, Token, TokenStream};

/// A cursor representing a position in the input source.
///
/// `Cursor` is a lightweight type that wraps a byte offset into the tokenizer's
/// input source. It's used by [`Checkpoint`] to track positions and is returned
/// by [`TokenStream::cursor`] to query the current position.
///
/// The cursor position represents:
/// - The byte offset in the input where the tokenizer will continue lexing
/// - If there are cached tokens, it points to the start of the first cached token
/// - Otherwise, it points to the position where the next token will be lexed from
pub struct Cursor<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> {
  pub(crate) cursor: usize,
  _input: &'s TokenStream<'a, T, L, C>,
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> core::fmt::Debug for Cursor<'a, '_, T, L, C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "Cursor({})", self.cursor)
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> Clone for Cursor<'a, '_, T, L, C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, T: Token<'a>, L: Lexer<'a, T>, C> Copy for Cursor<'a, '_, T, L, C> {}

impl<'a, 's, T: Token<'a>, L: Lexer<'a, T>, C> Cursor<'a, 's, T, L, C> {
  /// Creates a new cursor.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub(super) const fn new(cursor: usize, tkn: &'s TokenStream<'a, T, L, C>) -> Self {
    Self {
      cursor,
      _input: tkn,
    }
  }

  /// Returns the byte offset position in the input source.
  ///
  /// This is the absolute position (in bytes) where the tokenizer is currently
  /// positioned or where it will resume lexing.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn position(&self) -> usize {
    self.cursor
  }
}
