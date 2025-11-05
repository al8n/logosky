use super::*;

/// An iterator over the tokens produced by a [`Tokenizer`].
#[derive(derive_more::From, derive_more::Into)]
pub struct IntoIter<'a, T: Token<'a>> {
  stream: Tokenizer<'a, T>,
}

impl<'a, T> IntoIter<'a, T>
where
  T: Token<'a>,
{
  pub(super) const fn new(stream: Tokenizer<'a, T>) -> Self {
    Self { stream }
  }
}

impl<'a, T: Token<'a>> Clone for IntoIter<'a, T>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      stream: self.stream.clone(),
    }
  }
}

impl<'a, T> core::fmt::Debug for IntoIter<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.stream.fmt(f)
  }
}

impl<'a, T> IntoIterator for Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  type Item = Lexed<'a, T>;
  type IntoIter = IntoIter<'a, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.into_iter()
  }
}

impl<'a, T> Iterator for IntoIter<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  type Item = Lexed<'a, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn next(&mut self) -> Option<Self::Item> {
    let mut cursor = self.stream.cursor;
    Tokenizer::next_maybe(&mut self.stream, &mut cursor)
  }
}

/// An iterator over the tokens produced by a [`Tokenizer`].
#[derive(derive_more::From, derive_more::Into)]
pub struct Iter<'a, 'b, T: Token<'a>> {
  stream: &'b mut Tokenizer<'a, T>,
}

impl<'a, 'b, T> Iter<'a, 'b, T>
where
  T: Token<'a>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub(super) const fn new(stream: &'b mut Tokenizer<'a, T>) -> Self {
    Self { stream }
  }
}

impl<'a, 'b, T> IntoIterator for &'b mut Tokenizer<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  type Item = Lexed<'a, T>;
  type IntoIter = Iter<'a, 'b, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<'a, T> Iterator for Iter<'a, '_, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Copy,
{
  type Item = Lexed<'a, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn next(&mut self) -> Option<Self::Item> {
    let mut cursor = self.stream.cursor;
    Tokenizer::next_maybe(self.stream, &mut cursor)
  }
}
