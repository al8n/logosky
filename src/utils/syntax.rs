//! Syntax definition and incomplete syntax error types.
//!
//! This module provides types for representing syntax elements with a known number
//! of components, and errors for tracking missing components during parsing.
//!
//! # Design Philosophy
//!
//! When parsing syntax elements that require multiple components (like variable declarations,
//! function definitions, etc.), it's valuable to track *all* missing components rather than
//! failing on the first missing one. This enables:
//!
//! - Better error messages showing all missing parts
//! - Faster development iteration (see all errors at once)
//! - More helpful IDE diagnostics
//!
//! # Examples
//!
//! ```rust
//! # {
//! use logosky::{utils::{syntax::Syntax, typenum::U3, Span}, error::IncompleteSyntax};
//! use core::fmt;
//!
//! #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! struct MyLanguage;
//!
//! #[derive(Debug, Clone, PartialEq, Eq, Hash)]
//! enum WhileComponent {
//!     WhileKeyword,
//!     Condition,
//!     Body,
//! }
//!
//! impl fmt::Display for WhileComponent {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         match self {
//!             Self::WhileKeyword => write!(f, "'while' keyword"),
//!             Self::Condition => write!(f, "condition"),
//!             Self::Body => write!(f, "body"),
//!         }
//!     }
//! }
//!
//! struct WhileLoop;
//!
//! impl Syntax for WhileLoop {
//!     type Lang = MyLanguage;
//!     type Component = WhileComponent;
//!     type COMPONENTS = U3;
//!     type REQUIRED = U3;
//!
//!     fn possible_components() -> generic_array::GenericArray<Self::Component, U3> {
//!         [
//!             WhileComponent::WhileKeyword,
//!             WhileComponent::Condition,
//!             WhileComponent::Body,
//!         ].into_iter().collect()
//!     }
//!
//!     fn required_components() -> generic_array::GenericArray<Self::Component, Self::REQUIRED> {
//!         [
//!             WhileComponent::WhileKeyword,
//!             WhileComponent::Condition,
//!             WhileComponent::Body,
//!         ].into_iter().collect()
//!     }
//! }
//!
//! let mut error = IncompleteSyntax::<WhileLoop>::new(Span::new(10, 15), WhileComponent::Condition);
//! assert_eq!(error.len(), 1);
//! # }
//! ```
use generic_array::{ArrayLength, GenericArray};

use core::{
  fmt::{Debug, Display},
  hash::Hash,
};

/// A trait representing a syntax with a type-level number of components.
///
/// This trait defines the structure of a syntax element that has a known number
/// of required components. It uses `typenum` for type-level component count,
/// enabling compile-time arithmetic and better integration with generic-array-based code.
///
/// # Type Parameters
///
/// - `Component`: The type representing individual syntax components (usually an enum)
/// - `COMPONENTS`: A type-level unsigned integer (via `ArrayLength`) specifying component count
///
/// # Examples
///
/// ```rust
/// # {
/// use logosky::utils::{syntax::Syntax, typenum};
/// use typenum::U5;
/// use core::fmt;
///
/// struct MyLanguage;
///
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// enum LetStatementComponent {
///     LetKeyword,
///     Identifier,
///     Equals,
///     Expression,
///     Semicolon,
/// }
///
/// impl fmt::Display for LetStatementComponent {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         match self {
///             Self::LetKeyword => write!(f, "'let' keyword"),
///             Self::Identifier => write!(f, "identifier"),
///             Self::Equals => write!(f, "'=' operator"),
///             Self::Expression => write!(f, "expression"),
///             Self::Semicolon => write!(f, "';' semicolon"),
///         }
///     }
/// }
///
/// struct LetStatement;
///
/// impl Syntax for LetStatement {
///     type Lang = MyLanguage;
///     type Component = LetStatementComponent;
///     type COMPONENTS = U5;
///     type REQUIRED = U5;
///
///     fn possible_components() -> generic_array::GenericArray<Self::Component, Self::COMPONENTS> {
///         [
///             LetStatementComponent::LetKeyword,
///             LetStatementComponent::Identifier,
///             LetStatementComponent::Equals,
///             LetStatementComponent::Expression,
///             LetStatementComponent::Semicolon,
///         ].into_iter().collect()
///     }
///
///     fn required_components() -> generic_array::GenericArray<Self::Component, Self::REQUIRED> {
///         [
///             LetStatementComponent::LetKeyword,
///             LetStatementComponent::Identifier,
///             LetStatementComponent::Equals,
///             LetStatementComponent::Expression,
///             LetStatementComponent::Semicolon,
///         ].into_iter().collect()
///     }
/// }
/// # }
/// ```
pub trait Syntax {
  /// The language this syntax belongs to.
  type Lang;

  /// The component type of this syntax.
  ///
  /// Usually this is an enum representing different variants of syntax components.
  /// This type is used for error reporting to specify which components are missing.
  type Component: Display + Debug + Clone + PartialEq + Eq + Hash;

  /// The number of components in this syntax, represented as a type-level unsigned integer.
  ///
  /// Uses `typenum` to represent the count at the type level, enabling compile-time
  /// arithmetic without requiring unstable `generic_const_exprs` feature.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use typenum::U3; // For a syntax with 3 components
  ///
  /// impl Syntax for MySyntax {
  ///     type COMPONENTS = U3;
  ///     // ...
  /// }
  /// ```
  type COMPONENTS: ArrayLength + Debug + Eq + Hash;

  /// The number of required components in this syntax, represented as a type-level unsigned integer.
  ///
  /// Uses `typenum` to represent the count at the type level, enabling compile-time
  /// arithmetic without requiring unstable `generic_const_exprs` feature.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use typenum::U3; // For a syntax with 3 components
  ///
  /// impl Syntax for MySyntax {
  ///     type COMPONENTS = U3;
  ///     // ...
  /// }
  /// ```
  type REQUIRED: ArrayLength + Debug + Eq + Hash;

  /// Returns an array containing all possible components for this syntax.
  ///
  /// The array should contain all components that can be part of this syntax element,
  /// in a canonical order.
  fn possible_components() -> GenericArray<Self::Component, Self::COMPONENTS>;

  /// Returns an array containing all required components for this syntax.
  ///
  /// The array should contain all components that are required for this syntax element,
  /// in a canonical order.
  fn required_components() -> GenericArray<Self::Component, Self::REQUIRED>;
}
