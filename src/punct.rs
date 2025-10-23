/// Defines the punctuators.
///
/// # Examples
/// ```rust
/// use logosky::punctuator;
///
/// punctuator! {
///   (LAngle, "L_ANGLE", "<"),
///   (RAngle, "R_ANGLE", ">"),
/// }
/// ```
#[macro_export]
macro_rules! punctuator {
  ($(($name:ident, $syntax_tree_display: literal, $punct:literal)),+$(,)?) => {
    paste::paste! {
      $(
        #[doc = "The `" $punct "` punctuator"]
        #[derive(::core::fmt::Debug, ::core::clone::Clone, ::core::marker::Copy, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
        pub struct $name<S = $crate::__private::utils::Span, C = ()> {
          span: S,
          source: C,
        }

        impl<S> $name<S> {
          /// Creates a new punctuator with the given span.
          #[cfg_attr(not(tarpaulin), inline(always))]
          pub const fn new(span: S) -> Self {
            Self { span, source: () }
          }
        }

        impl<S, C> $name<S, C> {
          #[doc = "Creates a new `" $punct "` punctuator with the given span and content."]
          #[cfg_attr(not(tarpaulin), inline(always))]
          pub const fn with_content(span: S, content: C) -> Self {
            Self { span, source: content }
          }

          #[doc = "Returns the raw string literal of the `" $punct "` punctuator."]
          #[inline]
          pub const fn raw() -> &'static ::core::primitive::str {
            $punct
          }

          #[doc = "Returns the raw string literal of the `" $punct "` punctuator."]
          #[inline]
          pub const fn as_str(&self) -> &'static ::core::primitive::str {
            Self::raw()
          }

          #[doc = "Returns the span of the `" $punct "` punctuator."]
          #[inline]
          pub const fn span(&self) -> &S {
            &self.span
          }

          #[doc = "Returns a reference to the content of the `" $punct "` punctuator."]
          #[inline]
          pub const fn content(&self) -> &C {
            &self.source
          }
        }

        impl<S, C> ::core::cmp::PartialEq<::core::primitive::str> for $name<S, C> {
          #[inline]
          fn eq(&self, other: &::core::primitive::str) -> bool {
            self.as_str().eq(other)
          }
        }

        impl<S, C> ::core::cmp::PartialOrd<::core::primitive::str> for $name<S, C> {
          #[inline]
          fn partial_cmp(&self, other: &::core::primitive::str) -> ::core::option::Option<::core::cmp::Ordering> {
            self.as_str().partial_cmp(other)
          }
        }

        impl<S, C> ::core::cmp::PartialEq<$name<S, C>> for ::core::primitive::str {
          #[inline]
          fn eq(&self, other: &$name<S, C>) -> bool {
            self.eq(other.as_str())
          }
        }

        impl<S, C> ::core::cmp::PartialOrd<$name<S, C>> for ::core::primitive::str {
          #[inline]
          fn partial_cmp(&self, other: &$name<S, C>) -> ::core::option::Option<::core::cmp::Ordering> {
            self.partial_cmp(other.as_str())
          }
        }

        impl<S, C> ::core::borrow::Borrow<::core::primitive::str> for $name<S, C> {
          #[inline]
          fn borrow(&self) -> &::core::primitive::str {
            self.as_str()
          }
        }

        impl<S, C> ::core::convert::AsRef<::core::primitive::str> for $name<S, C> {
          #[inline]
          fn as_ref(&self) -> &::core::primitive::str {
            self.as_str()
          }
        }

        impl<S, C> $crate::__private::utils::AsSpan<S> for $name<S, C> {
          #[inline]
          fn as_span(&self) -> &S {
            self.span()
          }
        }

        impl<S, C> $crate::__private::utils::IntoSpan<S> for $name<S, C> {
          #[inline]
          fn into_span(self) -> S {
            self.span
          }
        }

        impl<S, C> $crate::__private::utils::IntoComponents for $name<S, C> {
          type Components = (S, C);

          #[inline]
          fn into_components(self) -> Self::Components {
            (self.span, self.source)
          }
        }

        impl<S, C> ::core::fmt::Display for $name<S, C> {
          #[cfg_attr(not(tarpaulin), inline(always))]
          fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            ::core::fmt::Display::fmt($punct, f)
          }
        }

        impl<S, C> $crate::__private::utils::human_display::DisplayHuman for $name<S, C> {
          #[inline]
          fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            ::core::fmt::Display::fmt(self, f)
          }
        }

        impl<S, C> $crate::__private::utils::sdl_display::DisplayCompact for $name<S, C> {
          type Options = ();

          #[inline]
          fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>, _: &Self::Options) -> ::core::fmt::Result {
            ::core::fmt::Display::fmt(self, f)
          }
        }

        impl<S, C> $crate::__private::utils::sdl_display::DisplayPretty for $name<S, C> {
          type Options = ();

          #[inline]
          fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>, _: &Self::Options) -> ::core::fmt::Result {
            ::core::fmt::Display::fmt(self, f)
          }
        }
      )*
    }
  };
}
