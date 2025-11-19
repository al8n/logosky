pub use chumsky::*;
pub use tokenier::LogoStream;

/// Token parsers
pub mod token;

/// Generic purpose delimited by parsers
pub mod delimited;

/// Generic purpose separated by parsers
pub mod separated;

/// Skip recovery strategies
pub mod skip;

mod tokenier;

use super::{Token, utils::Spanned};

use crate::{
  KeywordToken, Lexed, Logos, Source,
  chumsky::{extra::ParserExtra, prelude::*},
  error::UnexpectedToken,
  utils::{Expected, cmp::Equivalent},
};

/// A trait for types that can be parsed from a token stream using Chumsky parsers.
///
/// `Parseable` provides a standardized way to define parsers for types that can be
/// constructed from a token stream. It enables composable, type-safe parsing where
/// each type knows how to parse itself, promoting modularity and reusability.
///
/// # Design Philosophy
///
/// This trait follows the principle of "parse, don't validate" - each type that implements
/// `Parseable` encapsulates both the structure and the parsing logic needed to construct
/// valid instances from tokens. This makes it easy to build complex parsers by composing
/// smaller, self-contained parsers.
///
/// # Error Recovery
///
/// `Parseable` uses **fail-fast** semantics by default: parsing stops at the first error
/// and returns immediately. For error recovery scenarios (IDE tooling, schema validation,
/// compiler-like diagnostics), use Chumsky's `.recover_with()` combinator along with
/// LogoSky's recovery utilities:
///
/// - **Delimited parsers**: `DelimitedByBrace::recoverable_parser(content)`, etc.
/// - **Skip utilities**: `skip_until_token()`, `skip_through_closing_delimiter()`, etc.
/// - **Recovery strategies**: `via_parser()`, `nested_delimiters()`, etc.
///
/// These primitives allow you to build parsers that collect multiple errors while
/// producing partial ASTs with placeholder nodes for malformed sections
///
/// # Type Parameters
///
/// - `'a`: The lifetime of the input source
/// - `I`: The input stream type (typically [`Tokenizer<'a, T>`](crate::Tokenizer))
/// - `T`: The token type being parsed
/// - `Error`: The error type produced during parsing
///
/// # Provided Implementations
///
/// LogoSky provides `Parseable` implementations for many common types:
///
/// - **`Spanned<D>`**: Wraps a parseable type with span information
/// - **`Option<D>`**: Makes any parseable type optional
/// - **`Vec<D>`**: Parses repeated occurrences of a type
/// - **`Box<D>`, `Rc<D>`, `Arc<D>`**: Smart pointer wrappers
/// - **`Either<L, R>`**: Choice between two parseable types (with `either` feature)
/// - **`Among<L, M, R>`**: Choice among three parseable types (with `among` feature)
///
/// # Examples
///
/// ## Basic Implementation
///
/// ```rust,ignore
/// use logosky::{Parseable, Tokenizer, Token};
/// use chumsky::prelude::*;
///
/// // Define a simple expression type
/// enum Expr {
///     Number(i64),
///     Add(Box<Expr>, Box<Expr>),
/// }
///
/// impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Expr
/// where
///     I: LogoStream<'a, T>,
///     T: Token<'a>,
///     Error: 'a,
/// {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone
///     where
///         E: extra::ParserExtra<'a, I, Error = Error> + 'a,
///     {
///         // Parse a number token
///         let number = any()
///             .try_map(|tok, _| match tok {
///                 Lexed::Token(t) if is_number(&t) => {
///                     Ok(Expr::Number(parse_number(&t)))
///                 }
///                 _ => Err(Error::expected_number()),
///             });
///
///         // Parse addition
///         recursive(|expr| {
///             number.or(expr.clone()
///                 .then_ignore(plus_token())
///                 .then(expr)
///                 .map(|(l, r)| Expr::Add(Box::new(l), Box::new(r))))
///         })
///     }
/// }
/// ```
///
/// ## Using Provided Implementations
///
/// ```rust,ignore
/// // Parse optional expressions
/// type OptionalExpr = Option<Expr>;
/// let parser = OptionalExpr::parser(); // Automatically derives from Expr::parser()
///
/// // Parse a list of expressions
/// type ExprList = Vec<Expr>;
/// let parser = ExprList::parser(); // Parses repeated expressions
///
/// // Parse an expression with span information
/// type SpannedExpr = Spanned<Expr>;
/// let parser = SpannedExpr::parser(); // Adds span tracking
/// ```
///
/// ## Composing Parseable Types
///
/// ```rust,ignore
/// // A statement can be an expression or a declaration
/// enum Statement {
///     Expr(Expr),
///     Decl(Declaration),
/// }
///
/// impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Statement
/// where
///     I: LogoStream<'a, T>,
///     T: Token<'a>,
///     Expr: Parseable<'a, I, T, Error>,
///     Declaration: Parseable<'a, I, T, Error>,
///     Error: 'a,
/// {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone
///     where
///         E: extra::ParserExtra<'a, I, Error = Error> + 'a,
///     {
///         // Compose parsers from parseable types
///         Expr::parser().map(Statement::Expr)
///             .or(Declaration::parser().map(Statement::Decl))
///     }
/// }
/// ```
///
/// # Benefits
///
/// - **Modularity**: Each type encapsulates its own parsing logic
/// - **Composability**: Complex parsers are built from simple, reusable parts
/// - **Type Safety**: The type system ensures parsers are correctly composed
/// - **Maintainability**: Parsing logic lives with the data structures it creates
pub trait Parseable<'a, I, T, Error> {
  /// Returns a parser that can parse `Self` from the given token stream.
  ///
  /// This method constructs a Chumsky parser that knows how to parse the implementing
  /// type from a stream of tokens. The parser is composable and can be used with other
  /// Chumsky combinators.
  ///
  /// # Type Parameters
  ///
  /// - `E`: The parser extra type that carries error and state information
  ///
  /// # Returns
  ///
  /// A Chumsky parser that produces `Self` on success or an error of type `Error` on failure.
  ///
  /// # Example
  ///
  /// ```rust,ignore
  /// // Get a parser for MyType
  /// let parser = MyType::parser::<extra::Err<MyError>>();
  ///
  /// // Use it to parse a token stream
  /// let stream = Tokenizer::new(input);
  /// match parser.parse(stream).into_result() {
  ///     Ok(value) => println!("Parsed: {:?}", value),
  ///     Err(errors) => println!("Parse errors: {:?}", errors),
  /// }
  /// ```
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a;
}

impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for Spanned<D>
where
  D: Parseable<'a, I, T, Error>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
    I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
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
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
  where
    Self: Sized + 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
    I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
  {
    use chumsky::Parser;

    <D as Parseable<'a, I, T, Error>>::parser().or_not()
  }
}

#[cfg(any(feature = "std", feature = "alloc"))]
const _: () = {
  use crate::utils::Span;

  macro_rules! wrapper_parser {
    ($($ty:ty),+$(,)?) => {
      $(
        impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for $ty
        where
          D: Parseable<'a, I, T, Error>,
          I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
          T: Token<'a>,
          Error: 'a,
        {
          #[cfg_attr(not(tarpaulin), inline(always))]
          fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
          where
            Self: Sized + 'a,
            E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
          {
            use chumsky::Parser;

            <D as Parseable<'a, I, T, Error>>::parser().map(<$ty>::from)
          }
        }

        impl<D> $crate::utils::AsSpan<Span> for $ty
        where
          D: $crate::utils::AsSpan<Span>,
        {
          #[cfg_attr(not(tarpaulin), inline(always))]
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

  impl<D> crate::utils::IntoSpan<Span> for std::boxed::Box<D>
  where
    D: crate::utils::IntoSpan<Span>,
  {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_span(self) -> Span {
      (*self).into_span()
    }
  }

  impl<'a, D, I, T, Error> Parseable<'a, I, T, Error> for std::vec::Vec<D>
  where
    D: Parseable<'a, I, T, Error>,
    I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: Token<'a>,
    Error: 'a,
  {
    #[cfg_attr(not(tarpaulin), inline(always))]
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
};

const _: () = {
  use crate::utils::{AsSpan, IntoSpan, Span};
  use either::Either;

  impl<'a, L, R, I, T, Error> Parseable<'a, I, T, Error> for Either<L, R>
  where
    L: Parseable<'a, I, T, Error>,
    R: Parseable<'a, I, T, Error>,
  {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
    where
      Self: Sized + 'a,
      E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
      I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
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
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
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
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
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

  use crate::utils::{AsSpan, IntoSpan, Span};

  impl<'a, L, M, R, I, T, Error> Parseable<'a, I, T, Error> for Among<L, M, R>
  where
    L: Parseable<'a, I, T, Error>,
    M: Parseable<'a, I, T, Error>,
    R: Parseable<'a, I, T, Error>,
  {
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn parser<E>() -> impl chumsky::Parser<'a, I, Self, E> + Clone
    where
      Self: Sized + 'a,
      E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a,
      I: LogoStream<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
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
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
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
    #[cfg_attr(test, inline)]
    #[cfg_attr(not(test), inline(always))]
    fn into_span(self) -> Span {
      match self {
        Self::Left(l) => l.into_span(),
        Self::Middle(m) => m.into_span(),
        Self::Right(r) => r.into_span(),
      }
    }
  }
};
