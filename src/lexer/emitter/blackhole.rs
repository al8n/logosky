use crate::utils::Spanned;

use super::{super::BlackHole, Emitter, Token};

impl<'a, T> Emitter<'a, T> for BlackHole
where
  T: Token<'a>,
{
  type Error = core::convert::Infallible;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_token_error(&mut self, _err: Spanned<T::Error>) -> Result<(), Self::Error> {
    Ok(())
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn emit_error(&mut self, _err: Spanned<Self::Error>) -> Result<(), Self::Error> {
    Ok(())
  }
}
