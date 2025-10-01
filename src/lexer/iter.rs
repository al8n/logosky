use super::*;

/// An iterator over the tokens produced by a [`logos::Lexer`].
#[derive(derive_more::From, derive_more::Into)]
pub struct Iter<'a, T: Token<'a>> {
  logos: logos::Lexer<'a, T::Logos>,
}

impl<'a, T: Token<'a>> Clone for Iter<'a, T>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  #[inline(always)]
  fn clone(&self) -> Self {
    Self {
      logos: self.logos.clone(),
    }
  }
}

impl<'a, T> core::fmt::Debug for Iter<'a, T>
where
  T: Token<'a>,
  <T::Logos as Logos<'a>>::Source: core::fmt::Debug,
  <T::Logos as Logos<'a>>::Extras: core::fmt::Debug,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.logos.fmt(f)
  }
}

impl<'a, T: Token<'a>> IntoIterator for TokenStream<'a, T> {
  type Item = Lexed<'a, T>;
  type IntoIter = Iter<'a, T>;

  #[inline(always)]
  fn into_iter(self) -> Self::IntoIter {
    let logos = logos::Lexer::<T::Logos>::with_extras(self.input, self.state);
    Iter { logos }
  }
}

impl<'a, T: Token<'a>> IntoIterator for &'a TokenStream<'a, T>
where
  <T::Logos as Logos<'a>>::Extras: Clone,
{
  type Item = Lexed<'a, T>;
  type IntoIter = Iter<'a, T>;

  #[inline(always)]
  fn into_iter(self) -> Self::IntoIter {
    let logos = logos::Lexer::<T::Logos>::with_extras(self.input, self.state.clone());
    Iter { logos }
  }
}

impl<'a, T> Iterator for Iter<'a, T>
where
  T: Token<'a>,
{
  type Item = Lexed<'a, T>;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    Lexed::lex(&mut self.logos)
  }
}
