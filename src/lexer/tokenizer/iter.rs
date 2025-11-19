use super::*;

/// An iterator over the tokens produced by a [`Tokenizer`].
#[derive(derive_more::From, derive_more::Into)]
pub struct IntoIter<'a, T: Token<'a>, C> {
  stream: Tokenizer<'a, T, C>,
}

impl<'a, T, C> IntoIter<'a, T, C>
where
  T: Token<'a>,
{
  pub(super) const fn new(stream: Tokenizer<'a, T, C>) -> Self {
    Self { stream }
  }
}

impl<'a, T: Token<'a>, C> Clone for IntoIter<'a, T, C>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      stream: self.stream.clone(),
    }
  }
}

impl<'a, T, C> core::fmt::Debug for IntoIter<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
  C: core::fmt::Debug,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.stream.fmt(f)
  }
}

impl<'a, T, C> IntoIterator for Tokenizer<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Cache<'a, T>,
{
  type Item = Spanned<Lexed<'a, T>>;
  type IntoIter = IntoIter<'a, T, C>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.into_iter()
  }
}

impl<'a, T, C> Iterator for IntoIter<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Cache<'a, T>,
{
  type Item = Spanned<Lexed<'a, T>>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn next(&mut self) -> Option<Self::Item> {
    Tokenizer::next(&mut self.stream)
  }
}

/// An iterator over the tokens produced by a [`Tokenizer`].
#[derive(derive_more::From, derive_more::Into)]
pub struct Iter<'a, 'b, T: Token<'a>, C> {
  stream: &'b mut Tokenizer<'a, T, C>,
}

impl<'a, 'b, T, C> Iter<'a, 'b, T, C>
where
  T: Token<'a>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub(super) const fn new(stream: &'b mut Tokenizer<'a, T, C>) -> Self {
    Self { stream }
  }
}

impl<'a, 'b, T, C> IntoIterator for &'b mut Tokenizer<'a, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Cache<'a, T>,
{
  type Item = Spanned<Lexed<'a, T>>;
  type IntoIter = Iter<'a, 'b, T, C>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<'a, T, C> Iterator for Iter<'a, '_, T, C>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Extras: Clone,
  C: Cache<'a, T>,
{
  type Item = Spanned<Lexed<'a, T>>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn next(&mut self) -> Option<Self::Item> {
    Tokenizer::next(self.stream)
  }
}
