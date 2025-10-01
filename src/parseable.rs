use logos::{Logos, Source};

use super::{
  Token, Tokenizer,
  utils::{AsSpan, IntoSpan, Span, Spanned},
};

/// A trait for types that can be parsed directly from a [`I: Tokenizer<'a, T>`](Tokenizer) which yields [`T: Token<'a>`](Token) and may produce an `Error`.
pub trait Parseable<'a, I, T, Error> {
  /// Returns a parser that can parse `Self` from the given tokenizer.
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a;
}

impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for Spanned<D>
where
  D: Parseable<'a, I, T, Error>,
{
  #[inline(always)]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
    I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
  {
    use chumsky::Parser;

    <D as Parseable<'a, I, T, Error>>::parser()
      .map_with(|value, exa| Spanned::new(exa.span(), value))
  }
}

impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for Option<D>
where
  D: Parseable<'a, I, T, Error> + 'a,
{
  #[inline(always)]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
    I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
  {
    use chumsky::Parser;

    <D as Parseable<'a, I, T, Error>>::parser().or_not()
  }
}

macro_rules! wrapper_parser {
  ($($ty:ty),+$(,)?) => {
    $(
      impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for $ty
      where
        D: Parseable<'a, I, T, Error>,
        I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
        T: Token<'a>,
        Error: 'a,
      {
        #[inline(always)]
        fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
        where
          Self: Sized + 'a,
          E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
        {
          use chumsky::Parser;

          <D as Parseable<'a, I, T, Error>>::parser().map(<$ty>::from)
        }
      }

      impl<D> AsSpan<Span> for $ty
      where
        D: AsSpan<Span>,
      {
        #[inline(always)]
        fn as_span(&self) -> &Span {
          self.as_ref().as_span()
        }
      }
    )*
  };
}

wrapper_parser! {
  std::boxed::Box<D>,
  std::rc::Rc<D>,
  std::sync::Arc<D>,
}

impl<D> IntoSpan<Span> for std::boxed::Box<D>
where
  D: IntoSpan<Span>,
{
  #[inline(always)]
  fn into_span(self) -> Span {
    (*self).into_span()
  }
}

impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for std::vec::Vec<D>
where
  D: Parseable<'a, I, T, Error>,
  I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
  T: Token<'a>,
  Error: 'a,
{
  #[inline(always)]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
  {
    use chumsky::{IterParser, Parser};

    <D as Parseable<'a, I, T, Error>>::parser()
      .repeated()
      .collect()
  }
}

#[cfg(feature = "either")]
const _: () = {
  use crate::utils::{AsSpan, IntoSpan};
  use either::Either;

  impl<'a, L, R, I, T, Error> Parseable<'a, I, T, Error> for Either<L, R>
  where
    L: Parseable<'a, I, T, Error>,
    R: Parseable<'a, I, T, Error>,
  {
    #[inline(always)]
    fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
    where
      Self: Sized + 'a,
      E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
      I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
      T: Token<'a>,
      Error: 'a,
    {
      use chumsky::Parser;

      L::parser()
        .map(Either::Left)
        .or(R::parser().map(Either::Right))
    }
  }

  impl<L, R> AsSpan<Span> for Either<L, R>
  where
    L: AsSpan<Span>,
    R: AsSpan<Span>,
  {
    #[inline(always)]
    fn as_span(&self) -> &Span {
      match self {
        Either::Left(l) => l.as_span(),
        Either::Right(r) => r.as_span(),
      }
    }
  }

  impl<L, R> IntoSpan<Span> for Either<L, R>
  where
    L: IntoSpan<Span>,
    R: IntoSpan<Span>,
  {
    #[inline(always)]
    fn into_span(self) -> Span {
      match self {
        Either::Left(l) => l.into_span(),
        Either::Right(r) => r.into_span(),
      }
    }
  }
};

#[cfg(feature = "among")]
const _: () = {
  use among::Among;

  use crate::utils::{AsSpan, IntoSpan};

  impl<'a, L, M, R, I, T, Error> Parseable<'a, I, T, Error> for Among<L, M, R>
  where
    L: Parseable<'a, I, T, Error>,
    M: Parseable<'a, I, T, Error>,
    R: Parseable<'a, I, T, Error>,
  {
    #[inline(always)]
    fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
    where
      Self: Sized + 'a,
      E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
      I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
      T: Token<'a>,
      Error: 'a,
    {
      use chumsky::prelude::*;

      choice((
        L::parser().map(Self::Left),
        M::parser().map(Self::Middle),
        R::parser().map(Self::Right),
      ))
    }
  }

  impl<L, M, R> AsSpan<Span> for Among<L, M, R>
  where
    L: AsSpan<Span>,
    M: AsSpan<Span>,
    R: AsSpan<Span>,
  {
    #[inline(always)]
    fn as_span(&self) -> &Span {
      match self {
        Self::Left(l) => l.as_span(),
        Self::Middle(m) => m.as_span(),
        Self::Right(r) => r.as_span(),
      }
    }
  }

  impl<L, M, R> IntoSpan<Span> for Among<L, M, R>
  where
    L: IntoSpan<Span>,
    M: IntoSpan<Span>,
    R: IntoSpan<Span>,
  {
    #[inline(always)]
    fn into_span(self) -> Span {
      match self {
        Self::Left(l) => l.into_span(),
        Self::Middle(m) => m.into_span(),
        Self::Right(r) => r.into_span(),
      }
    }
  }
};
