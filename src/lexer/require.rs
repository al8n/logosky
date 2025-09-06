use super::Token;

/// A macro to create a parser fn for a specific token kind
///
/// ## Example
///
/// ```rust
/// use smear_utils::{require_token_parser_fn, lexer::token::require_token};
///
/// #[derive(Copy, Clone)]
/// struct MyTokenKindFoo;
///
/// #[derive(Copy, Clone)]
/// struct MyTokenKindBar;
///
/// require_token_parser_fn! {
///   /// Returns a parser which parses a MyTokenKindFoo token
///   pub fn foo<'src, I, E>() -> MyTokenKindFoo {
///     require_token(MyTokenKindFoo)
///   }
///
///   /// Returns a parser which parses a MyTokenKindBar token
///   pub fn bar<'src, I, E>() -> MyTokenKindBar {
///     require_token(MyTokenKindBar)
///   }
/// }
/// ```
#[macro_export]
macro_rules! require_token_parser_fn {
  (
    $(
      $(#[$meta:meta])*
      $vis:vis fn $name:ident<$lt:lifetime, $t:ident, $e:ident $(, $g:ident)*>($($args:ident: $arg_ty:ty),*) -> $tk:ty { $expr:expr }
    )*
  ) => {
    $(
      $(#[$meta])*
      #[allow(clippy::type_complexity)]
      $vis fn $name<$lt, $t, $e $(, $g)*>($($args: $arg_ty),*) -> impl $crate::__private::chumsky::Parser<
        $lt,
        $t,
        <
          <$t as $crate::__private::chumsky::input::Input<$lt>>::Token as $crate::__private::Require<
            $lt,
            $tk,
          >
        >::Output,
        $e,
      > + ::core::clone::Clone
      where
        $t: $crate::__private::Tokenizer<$lt>,
        <$t as $crate::__private::chumsky::input::Input<$lt>>::Token: $crate::__private::Require<
          $lt,
          $tk,
          Input = <$t as $crate::__private::chumsky::input::SliceInput<$lt>>::Slice,
          Span = <$t as $crate::__private::chumsky::input::Input<$lt>>::Span,
        >,
        <$t as $crate::__private::chumsky::input::Input<$lt>>::Token: $crate::__private::token::Token<
          $lt,
        >,
        $($g: ::core::marker::Copy + 'a,)*
        $e: $crate::__private::chumsky::extra::ParserExtra<$lt, $t>,
        <$e as $crate::__private::chumsky::extra::ParserExtra<$lt, $t>>::Error:
          $crate::__private::FromLexError<
            $lt,
            <$t as $crate::__private::chumsky::input::Input<$lt>>::Token,
            <$t as $crate::__private::chumsky::input::Input<$lt>>::Span,
          >,
      {
        $expr
      }
    )*
  };
}

/// A requirement for a spec.
pub trait Require<'a, Spec> {
  /// The input type of the requirement
  type Input: 'a;
  /// The output type of the requirement.
  type Output: 'a;
  /// The span type of the requirement.
  type Span: 'a;

  /// Requires the token to match the given specification, returning a lexer error if it does not.
  fn require(
    self,
    src: Self::Input,
    span: Self::Span,
    spec: Spec,
  ) -> Result<Self::Output, Self::Error>
  where
    Self: Token<'a>,
    Spec: Copy + 'a,
    Self::Output: 'a;
}
