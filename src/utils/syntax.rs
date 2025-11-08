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
//!     fn possible_components() -> logosky::utils::FrozenGenericVec<Self::Component, U3> {
//!         let mut vec = logosky::utils::GenericVec::new();
//!         vec.push(WhileComponent::WhileKeyword);
//!         vec.push(WhileComponent::Condition);
//!         vec.push(WhileComponent::Body);
//!         vec.freeze()
//!     }
//!
//!     fn required_components() -> logosky::utils::FrozenGenericVec<Self::Component, Self::REQUIRED> {
//!         let mut vec = logosky::utils::GenericVec::new();
//!         vec.push(WhileComponent::WhileKeyword);
//!         vec.push(WhileComponent::Condition);
//!         vec.push(WhileComponent::Body);
//!         vec.freeze()
//!     }
//! }
//!
//! let mut error = IncompleteSyntax::<WhileLoop>::new(Span::new(10, 15), WhileComponent::Condition);
//! assert_eq!(error.len(), 1);
//! # }
//! ```
use generic_array::ArrayLength;

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
///     fn possible_components() -> logosky::utils::FrozenGenericVec<Self::Component, Self::COMPONENTS> {
///         let mut vec = logosky::utils::GenericVec::new();
///         vec.push(LetStatementComponent::LetKeyword);
///         vec.push(LetStatementComponent::Identifier);
///         vec.push(LetStatementComponent::Equals);
///         vec.push(LetStatementComponent::Expression);
///         vec.push(LetStatementComponent::Semicolon);
///         vec.freeze()
///     }
///
///     fn required_components() -> logosky::utils::FrozenGenericVec<Self::Component, Self::REQUIRED> {
///         let mut vec = logosky::utils::GenericVec::new();
///         vec.push(LetStatementComponent::LetKeyword);
///         vec.push(LetStatementComponent::Identifier);
///         vec.push(LetStatementComponent::Equals);
///         vec.push(LetStatementComponent::Expression);
///         vec.push(LetStatementComponent::Semicolon);
///         vec.freeze()
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

  /// Returns a frozen vector containing all possible components for this syntax.
  ///
  /// The vector contains all components that can be part of this syntax element,
  /// in a canonical order. The returned vector is immutable but can be consumed
  /// via `IntoIterator`.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// let components = MySyntax::possible_components();
  /// for component in components.iter() {
  ///     println!("{}", component);
  /// }
  /// ```
  fn possible_components() -> crate::utils::FrozenGenericVec<Self::Component, Self::COMPONENTS>;

  /// Returns a frozen vector containing all required components for this syntax.
  ///
  /// The vector contains all components that are required for this syntax element,
  /// in a canonical order. The returned vector is immutable but can be consumed
  /// via `IntoIterator`.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// let required = MySyntax::required_components();
  /// assert_eq!(required.len(), 2);
  /// ```
  fn required_components() -> crate::utils::FrozenGenericVec<Self::Component, Self::REQUIRED>;
}

/// A trait representing an AST node associated with a syntax definition.
///
/// This trait creates a type-level bridge between AST node types and their corresponding
/// `Syntax` types, enabling generic, type-safe error handling and parser implementation.
/// By associating an AST node with its syntax structure, we can automatically derive
/// error construction logic and write language-polymorphic parsers.
///
/// # Design Philosophy
///
/// When parsing AST nodes, incomplete syntax errors need to know which syntax element
/// failed to parse. The `AstNode` trait makes this relationship explicit at the type level:
///
/// - Each AST node type declares its corresponding `Syntax` type
/// - Generic code can use `T::Syntax` to construct appropriate `IncompleteSyntax<T::Syntax>` errors
/// - The `Lang` parameter enables the same structural node (e.g., `Name<S>`) to have
///   different syntax types in different language dialects
///
/// # Benefits
///
/// 1. **Type Safety**: Impossible to construct errors with the wrong syntax type
/// 2. **Generic Parsers**: Write parsers that work for any `T: AstNode<Lang>`
/// 3. **Discoverability**: Given an AST node, easily find its syntax definition
/// 4. **Language Polymorphism**: Same node structure, different syntax per dialect
/// 5. **Reduced Boilerplate**: Generic error handling without manual trait implementations
///
/// # Type Parameters
///
/// - `Lang`: The language or dialect this AST node belongs to. This enables:
///   - Distinguishing GraphQL from GraphQLx nodes
///   - Supporting multiple language dialects in one codebase
///   - Language-specific syntax customization
///
/// # Examples
///
/// ## Basic Implementation
///
/// ```rust
/// # {
/// use logosky::{utils::{syntax::{Syntax, AstNode}, typenum::U2, Span}, error::IncompleteSyntax};
/// use generic_array::GenericArray;
/// use core::fmt;
///
/// // Define a language
/// #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// struct MyLanguage;
///
/// // Define syntax components
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// enum VariableComponent {
///     Dollar,
///     Name,
/// }
///
/// impl fmt::Display for VariableComponent {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         match self {
///             Self::Dollar => write!(f, "'$' prefix"),
///             Self::Name => write!(f, "variable name"),
///         }
///     }
/// }
///
/// // Define syntax type
/// struct VariableSyntax;
///
/// impl Syntax for VariableSyntax {
///     type Lang = MyLanguage;
///     type Component = VariableComponent;
///     type COMPONENTS = U2;
///     type REQUIRED = U2;
///
///     fn possible_components() -> logosky::utils::FrozenGenericVec<Self::Component, Self::COMPONENTS> {
///         let mut vec = logosky::utils::GenericVec::new();
///         vec.push(VariableComponent::Dollar);
///         vec.push(VariableComponent::Name);
///         vec.freeze()
///     }
///
///     fn required_components() -> logosky::utils::FrozenGenericVec<Self::Component, Self::REQUIRED> {
///         let mut vec = logosky::utils::GenericVec::new();
///         vec.push(VariableComponent::Dollar);
///         vec.push(VariableComponent::Name);
///         vec.freeze()
///     }
/// }
///
/// // Define AST node
/// struct Variable {
///     name: String,
/// }
///
/// // Implement AstNode to bridge AST and Syntax
/// impl AstNode<MyLanguage> for Variable {
///     type Syntax = VariableSyntax;
/// }
///
/// // Now generic code can use T::Syntax automatically
/// fn create_incomplete_error<T>(span: Span, component: <T::Syntax as Syntax>::Component) -> IncompleteSyntax<T::Syntax>
/// where
///     T: AstNode<MyLanguage>,
/// {
///     IncompleteSyntax::new(span, component)
/// }
///
/// let error = create_incomplete_error::<Variable>(
///     Span::new(0, 3),
///     VariableComponent::Dollar
/// );
/// # }
/// ```
///
/// ## Generic Parser with AstNode
///
/// ```rust,ignore
/// use logosky::{
///     chumsky::{Parser, extra::ParserExtra},
///     utils::syntax::AstNode,
///     error::IncompleteSyntax,
/// };
///
/// // Generic parser that works for any AST node type
/// fn parse_node<'a, T, I, Token, Error, E>() -> impl Parser<'a, I, T, E>
/// where
///     T: AstNode<Lang> + Parseable<'a, I, Token, Error>,
///     Error: From<IncompleteSyntax<T::Syntax>>,
///     E: ParserExtra<'a, I, Error = Error>,
/// {
///     // Parser automatically knows how to construct errors using T::Syntax
///     T::parser()
///         .recover_with(|error| {
///             // Error recovery using T::Syntax automatically
///             // ...
///         })
/// }
/// ```
///
/// ## Language Polymorphism
///
/// ```rust,ignore
/// // Same structure, different syntax per language
/// struct Name<S> {
///     source: S,
/// }
///
/// // GraphQL implementation
/// impl<S> AstNode<GraphQL> for Name<S> {
///     type Syntax = GraphQLNameSyntax;
/// }
///
/// // GraphQLx implementation (extended dialect)
/// impl<S> AstNode<GraphQLx> for Name<S> {
///     type Syntax = GraphQLxNameSyntax; // Different syntax rules
/// }
/// ```
///
/// # Common Patterns
///
/// ## With Generic AST Nodes
///
/// For AST nodes with generic parameters, implement `AstNode` for the generic type:
///
/// ```rust,ignore
/// struct TypeDefinition<Name, Directives> {
///     name: Name,
///     directives: Option<Directives>,
/// }
///
/// impl<Name, Directives> AstNode<GraphQL> for TypeDefinition<Name, Directives> {
///     type Syntax = TypeDefinitionSyntax;
/// }
/// ```
///
/// ## Multiple Language Support
///
/// The same node structure can implement `AstNode` for multiple languages:
///
/// ```rust,ignore
/// impl<S> AstNode<GraphQL> for Variable<S> {
///     type Syntax = GraphQLVariableSyntax;
/// }
///
/// impl<S> AstNode<GraphQLx> for Variable<S> {
///     type Syntax = GraphQLxVariableSyntax;
/// }
/// ```
///
/// # See Also
///
/// - [`Syntax`]: Defines the structure and components of syntax elements
/// - [`IncompleteSyntax`]: Error type for tracking missing syntax components
/// - [`Parseable`]: Trait for types that can be parsed
pub trait AstNode<Lang> {
  /// The syntax type associated with this AST node.
  ///
  /// This type defines the structural components that make up the AST node during parsing.
  /// It must implement `Syntax<Lang = Lang>`, ensuring language consistency.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// impl AstNode<MyLanguage> for Variable {
  ///     type Syntax = VariableSyntax;
  ///     //             ^^^^^^^^^^^^^^
  ///     // This syntax type defines the components needed to parse a Variable
  /// }
  /// ```
  type Syntax: Syntax<Lang = Lang>;
}
