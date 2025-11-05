//! Syntax definition and incomplete syntax error types.
//!
//! This module provides types for representing syntax elements with a known number
//! of components, and errors for tracking missing components during parsing.
//!
//! Two implementations are provided:
//! - **Const-generic** (default): Uses `const COMPONENTS: usize` for component count
//! - **Type-level** (with `generic-array` feature): Uses `typenum` for type-level component count
//!
//! The implementation is chosen at compile time based on feature flags.
//!
//! # Feature Flags
//!
//! - Without `generic-array`: Uses const-generic implementation
//! - With `generic-array`: Uses type-level implementation with `generic_array::ArrayLength`
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
//! ## Const-Generic Version (Default)
//!
//! ```rust
//! # #[cfg(not(feature = "generic-array"))] {
//! use logosky::utils::syntax::{Syntax, IncompleteSyntax};
//! use core::fmt;
//!
//! #[derive(Debug, Clone, PartialEq, Eq, Hash)]
//! enum VarDeclComponent {
//!     VarKeyword,
//!     Identifier,
//!     TypeAnnotation,
//!     Initializer,
//! }
//!
//! impl fmt::Display for VarDeclComponent {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         match self {
//!             Self::VarKeyword => write!(f, "'var' keyword"),
//!             Self::Identifier => write!(f, "identifier"),
//!             Self::TypeAnnotation => write!(f, "type annotation"),
//!             Self::Initializer => write!(f, "initializer"),
//!         }
//!     }
//! }
//!
//! struct VarDecl;
//!
//! impl Syntax for VarDecl {
//!     type Component = VarDeclComponent;
//!     const COMPONENTS: usize = 4;
//!
//!     fn possible_components() -> [Self::Component; 4] {
//!         [
//!             VarDeclComponent::VarKeyword,
//!             VarDeclComponent::Identifier,
//!             VarDeclComponent::TypeAnnotation,
//!             VarDeclComponent::Initializer,
//!         ]
//!     }
//! }
//!
//! // Track missing components during parsing
//! let mut error = IncompleteSyntax::<VarDecl>::new(VarDeclComponent::Identifier);
//! error.push(VarDeclComponent::Initializer);
//!
//! // Error message shows all missing components
//! assert!(format!("{}", error).contains("identifier"));
//! assert!(format!("{}", error).contains("initializer"));
//! # }
//! ```
//!
//! ## Type-Level Version (with generic-array feature)
//!
//! ```rust
//! # #[cfg(feature = "generic-array")] {
//! use logosky::utils::syntax::{Syntax, IncompleteSyntax, typenum::U3};
//! use core::fmt;
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
//!     type Component = WhileComponent;
//!     type COMPONENTS = U3;
//!
//!     fn possible_components() -> generic_array::GenericArray<Self::Component, U3> {
//!         [
//!             WhileComponent::WhileKeyword,
//!             WhileComponent::Condition,
//!             WhileComponent::Body,
//!         ].into_iter().collect()
//!     }
//! }
//!
//! let mut error = IncompleteSyntax::<WhileLoop>::new(WhileComponent::Condition);
//! assert_eq!(error.len(), 1);
//! # }
//! ```

// Conditionally include the appropriate implementation
#[cfg(not(feature = "generic-array"))]
mod const_generic;
#[cfg(not(feature = "generic-array"))]
pub use const_generic::{IncompleteSyntax, Syntax};

#[cfg(feature = "generic-array")]
#[cfg_attr(docsrs, doc(cfg(feature = "generic-array")))]
mod type_level;
#[cfg(feature = "generic-array")]
#[cfg_attr(docsrs, doc(cfg(feature = "generic-array")))]
pub use type_level::{GenericArrayIter, IncompleteSyntax, typenum};
