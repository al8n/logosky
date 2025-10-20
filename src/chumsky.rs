pub use chumsky::*;

use logos::{Logos, Source};

use super::{Token, utils::Spanned};

pub use tokenier::LogoStream;

mod tokenier;

pub use skip::{skip_n_tokens, skip_until_any, skip_until_token, skip_while_token};

mod skip;

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
/// # Fail-Fast vs. Error Recovery
///
/// `Parseable` uses **fail-fast** semantics: parsing stops at the first error and returns
/// immediately. This is optimal for:
///
/// - **Runtime execution** (queries, mutations, subscriptions)
/// - **Performance-critical paths** where invalid input should be rejected quickly
/// - **Production systems** where partial results aren't useful
///
/// For **comprehensive error collection** (useful for IDE tooling, schema validation, and
/// compiler-like diagnostics), use the [`Recoverable`] trait instead. It collects all
/// errors while attempting to continue parsing, similar to how the Rust compiler reports
/// multiple errors in one pass.
///
/// ## When to Use Each
///
/// | Use Case | Trait | Behavior |
/// |----------|-------|----------|
/// | GraphQL query execution | `Parseable` | Stop at first error |
/// | GraphQL schema validation | `Recoverable` | Collect all errors |
/// | IDE error checking | `Recoverable` | Show all problems |
/// | Type definition parsing | `Recoverable` | Comprehensive diagnostics |
///
/// # See Also
///
/// - [`Recoverable`]: For comprehensive error collection with recovery
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

/// A trait for types that can be parsed with comprehensive error recovery.
///
/// `Recoverable` enables parsing that continues after encountering errors, collecting
/// multiple issues in a single pass. This is essential for tooling scenarios where
/// showing all problems at once provides a better user experience, similar to how
/// modern compilers (like Rust's `rustc`) report multiple errors instead of stopping
/// at the first one.
///
/// # Design Philosophy
///
/// While [`Parseable`] follows "fail-fast" semantics for production use, `Recoverable`
/// follows "fail-comprehensive" semantics for development tooling. The key differences:
///
/// - **Error Collection**: Accumulates all errors via Chumsky's error recovery
/// - **Continuation**: Uses `.recover_with()` to skip malformed sections and continue
/// - **Diagnostics**: Optimized for producing detailed error reports
/// - **Performance**: Trades speed for completeness (parses entire input even with errors)
///
/// # Use Cases
///
/// ## Schema Validation
///
/// When validating GraphQL schemas or type definitions, developers want to see all
/// issues at once rather than fixing errors one at a time:
///
/// ```graphql
/// type User {
///   name        # Error: Missing type annotation
///   age: Int
///   email       # Error: Missing type annotation
///   posts: [Post  # Error: Missing closing bracket
/// }
/// ```
///
/// With `Recoverable`, all three errors are reported in one pass.
///
/// ## IDE Integration
///
/// IDEs need to show red squiggles for all syntax errors simultaneously. Using
/// `Recoverable` allows the language server to:
///
/// - Parse the entire file even with errors
/// - Report diagnostics for all problems
/// - Provide accurate span information for each issue
/// - Enable features like "fix all" for common patterns
///
/// ## Compiler-Like Diagnostics
///
/// Tools like schema compilers and linters benefit from comprehensive error reporting:
///
/// - Show related errors together (e.g., missing fields in multiple type definitions)
/// - Provide context-aware suggestions for all issues
/// - Enable batch fixes and automated refactoring
///
/// # Implementation Pattern
///
/// Implementations should use Chumsky's recovery combinators:
///
/// ```rust,ignore
/// use logosky::chumsky::{Recoverable, Parser, prelude::*};
///
/// impl<'a, I, T, Error> Recoverable<'a, I, T, Error> for FieldDefinition {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone {
///         // Parse components with optional recovery
///         name_parser()
///             .then(colon_parser().or_not())
///             .then(type_parser().or_not())
///             .try_map_with(|(name, colon, ty), exa| {
///                 // Validate and collect errors
///                 if colon.is_none() {
///                     return Err(Error::missing_colon(exa.span()));
///                 }
///                 if ty.is_none() {
///                     return Err(Error::missing_type(exa.span()));
///                 }
///                 Ok(FieldDefinition { name, ty: ty.unwrap() })
///             })
///             .recover_with(via_parser(
///                 // On failure, skip to recovery point
///                 skip_until([Token::Newline, Token::RBrace])
///                     .to(FieldDefinition::placeholder())
///             ))
///     }
/// }
/// ```
///
/// # Recovery Strategies
///
/// Common recovery patterns:
///
/// - **`skip_until`**: Skip tokens until reaching a synchronization point (e.g., semicolons, braces)
/// - **`skip_then_retry_until`**: Skip and retry parsing at different positions
/// - **`nested_delimiters`**: Match delimiter pairs while respecting nesting
/// - **`via_parser`**: Use a custom recovery parser for domain-specific logic
///
/// # Error Accumulation
///
/// Errors are collected through Chumsky's `ParserExtra` mechanism. When a parser
/// fails and recovers:
///
/// 1. The error is recorded in the extra state
/// 2. The recovery strategy produces a placeholder value
/// 3. Parsing continues from the recovery point
/// 4. All collected errors are available in the final parse result
///
/// # Comparison with Parseable
///
/// | Aspect | `Parseable` | `Recoverable` |
/// |--------|-------------|---------------|
/// | **Semantics** | Fail-fast | Fail-comprehensive |
/// | **Error count** | First error only | All errors |
/// | **Performance** | Fast (early exit) | Slower (full parse) |
/// | **Recovery** | None | Via `.recover_with()` |
/// | **Use case** | Runtime execution | Development tooling |
/// | **Output** | Valid AST or error | AST (possibly with placeholders) + errors |
///
/// # When to Implement
///
/// Implement `Recoverable` for types that are:
///
/// - **Schema/SDL elements**: Type definitions, field definitions, directives
/// - **Top-level constructs**: Documents, definitions, declarations
/// - **IDE-visible**: Elements that users edit and want immediate feedback on
/// - **Validatable**: Elements where comprehensive checking adds value
///
/// **Don't implement** for:
///
/// - **Runtime queries**: Use `Parseable` instead (fail-fast for invalid queries)
/// - **Leaf tokens**: Simple terminals don't benefit from recovery
/// - **Performance-critical**: Tight loops where recovery overhead matters
///
/// # Examples
///
/// ## Basic Implementation
///
/// ```rust,ignore
/// use logosky::chumsky::{Recoverable, Parser, prelude::*};
///
/// struct TypeDefinition {
///     name: String,
///     fields: Vec<Field>,
/// }
///
/// impl<'a, I, T, Error> Recoverable<'a, I, T, Error> for TypeDefinition {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone {
///         // Parse with recovery
///         type_keyword()
///             .ignore_then(name_parser())
///             .then(fields_parser())
///             .map(|(name, fields)| TypeDefinition { name, fields })
///             .recover_with(skip_until([Token::TypeKeyword, Token::Eof]))
///     }
/// }
/// ```
///
/// ## Dual Implementation
///
/// Types can implement both traits for different contexts:
///
/// ```rust,ignore
/// // Fail-fast for query execution
/// impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Directive {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone {
///         // Strict parsing, no recovery
///         at_token()
///             .ignore_then(name_parser())
///             .then(arguments_parser())
///             .map(|(name, args)| Directive { name, args })
///     }
/// }
///
/// // Comprehensive for schema validation
/// impl<'a, I, T, Error> Recoverable<'a, I, T, Error> for Directive {
///     fn parser<E>() -> impl Parser<'a, I, Self, E> + Clone {
///         // With recovery for better diagnostics
///         at_token()
///             .ignore_then(name_parser())
///             .then(arguments_parser().or_not())
///             .try_map(/* validate and report errors */)
///             .recover_with(skip_until([Token::Newline]))
///     }
/// }
/// ```
///
/// # See Also
///
/// - [`Parseable`]: For fail-fast parsing in production scenarios
/// - [`IncompleteSyntax`](crate::error::IncompleteSyntax): For tracking missing syntax components
/// - [Chumsky recovery module](https://docs.rs/chumsky/latest/chumsky/recovery/): Recovery strategies
pub trait Recoverable<'a, I, T, Error> {
  /// Returns a parser with comprehensive error recovery.
  ///
  /// This method constructs a Chumsky parser that uses error recovery strategies
  /// to continue parsing after encountering errors. The parser collects all errors
  /// via Chumsky's error accumulation system and returns the parsed result (which
  /// may contain placeholder values for recovered sections).
  ///
  /// # Type Parameters
  ///
  /// - `E`: The parser extra type that carries error and state information
  ///
  /// # Returns
  ///
  /// A Chumsky parser that produces `Self` even in the presence of errors, with
  /// all encountered errors accumulated in the parser extra state.
  ///
  /// # Error Recovery
  ///
  /// Unlike [`Parseable::parser`], this parser:
  ///
  /// - Continues parsing after errors using `.recover_with()`
  /// - Accumulates multiple errors instead of stopping at the first
  /// - May return partial/placeholder values for malformed sections
  /// - Suitable for diagnostic tools and IDE integration
  ///
  /// # Example
  ///
  /// ```rust,ignore
  /// // Get a recovering parser for schema validation
  /// let parser = SchemaDefinition::parser::<extra::Err<SchemaError>>();
  ///
  /// // Parse a schema with multiple errors
  /// let result = parser.parse(tokenizer).into_output_errors();
  /// match result {
  ///     (Some(schema), errors) if errors.is_empty() => {
  ///         println!("Valid schema: {:?}", schema);
  ///     }
  ///     (schema_opt, errors) => {
  ///         // Show all errors to the user
  ///         for error in errors {
  ///             display_diagnostic(error);
  ///         }
  ///         // Can still use partial schema for some analysis
  ///         if let Some(schema) = schema_opt {
  ///             analyze_partial_schema(schema);
  ///         }
  ///     }
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

impl<'a, D, I, T, Error> Recoverable<'a, I, T, Error> for Option<D>
where
  D: Recoverable<'a, I, T, Error> + 'a,
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

    <D as Recoverable<'a, I, T, Error>>::parser().or_not()
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

        impl<'a, D, I, T, Error> Recoverable<'a, I, T, Error> for $ty
        where
          D: Recoverable<'a, I, T, Error>,
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

            <D as Recoverable<'a, I, T, Error>>::parser().map(<$ty>::from)
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

  impl<'a, D, I, T, Error> Recoverable<'a, I, T, Error> for std::vec::Vec<D>
  where
    D: Recoverable<'a, I, T, Error>,
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

      <D as Recoverable<'a, I, T, Error>>::parser()
        .repeated()
        .collect()
    }
  }
};

#[cfg(feature = "either")]
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

  impl<'a, L, R, I, T, Error> Recoverable<'a, I, T, Error> for Either<L, R>
  where
    L: Recoverable<'a, I, T, Error>,
    R: Recoverable<'a, I, T, Error>,
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

  impl<'a, L, M, R, I, T, Error> Recoverable<'a, I, T, Error> for Among<L, M, R>
  where
    L: Recoverable<'a, I, T, Error>,
    M: Recoverable<'a, I, T, Error>,
    R: Recoverable<'a, I, T, Error>,
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
