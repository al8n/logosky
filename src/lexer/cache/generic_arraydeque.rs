use core::mem::MaybeUninit;

use mayber::MaybeRef;

use super::{Cache, CachedToken, Checkpoint, Lexer, Token};

use generic_arraydeque::{ArrayLength, GenericArrayDeque};

impl<'a, T, L, N> Cache<'a, T, L> for GenericArrayDeque<CachedToken<'a, T, L>, N>
where
  T: Token<'a>,
  L: Lexer<'a, T>,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    self.len()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining(&self) -> usize {
    self.remaining_capacity()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn rewind(&mut self, ckp: &Checkpoint<'a, '_, T, L, Self>)
  where
    Self: Sized,
  {
    if self.is_empty() {
      return;
    }

    let cursor = ckp.cursor();
    // if the rewind position is before the start of the cache, clear the cache
    if let Some(span) = self.span_first() {
      if cursor.cursor < span.start() {
        self.clear();
        return;
      }

      // If the rewind position is exactly at the start of the cache, do nothing
      if cursor.cursor == span.start() {
        return;
      }
    }

    // if the rewind position is after the end of the cache, clear the cache
    if let Some(span) = self.span_last() {
      if cursor.cursor >= span.end() {
        self.clear();
        return;
      }
    }

    match self.binary_search_by_key(&cursor.cursor, |tok| tok.token().span().start()) {
      Ok(pos) => {
        self.retain(|tok| tok.token().span().start() >= pos);
      }
      Err(_) => {
        self.clear();
      }
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push_back(
    &mut self,
    tok: CachedToken<'a, T, L>,
  ) -> Result<&CachedToken<'a, T, L>, CachedToken<'a, T, L>> {
    match self.push_back_mut(tok) {
      Ok(tok) => Ok(tok),
      Err(tok) => Err(tok),
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_front(&mut self) -> Option<CachedToken<'a, T, L>> {
    self.pop_front()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop_back(&mut self) -> Option<CachedToken<'a, T, L>> {
    self.pop_back()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clear(&mut self) {
    self.clear();
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn peek<'p, 'b>(
    &'p self,
    buf: &'b mut [MaybeUninit<MaybeRef<'p, CachedToken<'a, T, L>>>],
  ) -> &'b mut [MaybeRef<'p, CachedToken<'a, T, L>>] {
    let fill = buf.len().min(self.len());
    for (i, tok) in self.iter().take(fill).enumerate() {
      buf[i].write(MaybeRef::Ref(tok));
    }

    unsafe {
      core::slice::from_raw_parts_mut(
        buf.as_mut_ptr() as *mut MaybeRef<'p, CachedToken<'a, T, L>>,
        fill,
      )
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn first(&self) -> Option<&CachedToken<'a, T, L>> {
    self.front()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn last(&self) -> Option<&CachedToken<'a, T, L>> {
    self.back()
  }
}
