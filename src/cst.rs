//! Concrete Syntax Tree (CST) utilities built on top of [rowan](https://docs.rs/rowan).
//!
//! This module provides infrastructure for building and working with typed concrete syntax trees.
//! Unlike Abstract Syntax Trees (ASTs), CSTs preserve all source information including whitespace,
//! comments, and exact token positions, making them ideal for:
//!
//! - **Code formatters**: Preserve exact formatting and whitespace
//! - **Linters**: Access complete source information for analysis
//! - **Language servers**: Provide accurate position information for IDE features
//! - **Refactoring tools**: Transform code while preserving formatting
//! - **Documentation generators**: Extract and preserve comments
//!
//! # Architecture
//!
//! The CST infrastructure has several key components:
//!
//! 1. **[`SyntaxTreeBuilder`](crate::cst::SyntaxTreeBuilder)**: Constructs CSTs from tokens using rowan's green tree builder
//! 2. **[`Parseable`](crate::cst::Parseable)**: Trait for types that can produce CST parsers
//! 3. **[`Node`](crate::cst::Node)**: Trait for typed CST nodes with zero-cost conversions
//! 4. **[`cast`](crate::cst::cast)**: Utility functions for working with CST nodes
//! 5. **[`error`](crate::cst::error)**: Error types for CST operations
//!
//! # Design Philosophy
//!
//! - **Zero-cost abstractions**: Typed CST nodes are just pointers, no runtime overhead
//! - **Lossless**: All source information is preserved in the tree
//! - **Immutable**: Trees are immutable by default (use `clone_for_update()` for mutations)
//! - **Type-safe**: Compile-time guarantees about node types and relationships
//!
//! # Basic Usage
//!
//! ```rust,ignore
//! use logosky::cst::{SyntaxTreeBuilder, Node, Parseable};
//! use rowan::Language;
//!
//! // 1. Define your language
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
//! enum SyntaxKind {
//!     Root,
//!     Identifier,
//!     Number,
//!     // ... other kinds
//! }
//!
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
//! struct MyLanguage;
//!
//! impl Language for MyLanguage {
//!     type Kind = SyntaxKind;
//!
//!     fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
//!         // Convert from rowan's raw kind
//!         todo!()
//!     }
//!
//!     fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
//!         // Convert to rowan's raw kind
//!         todo!()
//!     }
//! }
//!
//! // 2. Create a builder
//! let builder = SyntaxTreeBuilder::<MyLanguage>::new();
//!
//! // 3. Build the tree (usually done by a parser)
//! builder.start_node(SyntaxKind::Root);
//! builder.token(SyntaxKind::Identifier, "foo");
//! builder.finish_node();
//!
//! let green = builder.finish();
//! let root = SyntaxNode::new_root(green);
//! ```
//!
//! # Integration with Parsers
//!
//! The [`Parseable`](crate::cst::Parseable) trait integrates CST building with Chumsky parsers:
//!
//! ```rust,ignore
//! use logosky::cst::{Parseable, SyntaxTreeBuilder};
//!
//! struct Expression;
//!
//! impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Expression
//! where
//!     I: Tokenizer<'a, T>,
//!     T: LosslessToken<'a>,
//! {
//!     type Language = MyLanguage;
//!
//!     fn parser<E>(
//!         builder: &'a SyntaxTreeBuilder<Self::Language>,
//!     ) -> impl chumsky::Parser<'a, I, (), E> + Clone
//!     where
//!         E: chumsky::extra::ParserExtra<'a, I, Error = Error>,
//!     {
//!         // Return a parser that builds CST nodes
//!         todo!()
//!     }
//! }
//! ```
//!
//! # Working with Typed Nodes
//!
//! The [`Node`](crate::cst::Node) trait provides zero-cost typed wrappers around syntax nodes:
//!
//! ```rust,ignore
//! use logosky::cst::Node;
//!
//! #[derive(Debug)]
//! struct IdentifierNode {
//!     syntax: SyntaxNode<MyLanguage>,
//! }
//!
//! impl Node for IdentifierNode {
//!     type Language = MyLanguage;
//!     const KIND: SyntaxKind = SyntaxKind::Identifier;
//!
//!     fn can_cast(kind: SyntaxKind) -> bool {
//!         kind == Self::KIND
//!     }
//!
//!     fn try_cast(syntax: SyntaxNode<Self::Language>) -> Result<Self, error::SyntaxNodeMismatch<Self>> {
//!         if Self::can_cast(syntax.kind()) {
//!             Ok(Self { syntax })
//!         } else {
//!             Err(error::SyntaxNodeMismatch::new(Self::KIND, syntax))
//!         }
//!     }
//!
//!     fn syntax(&self) -> &SyntaxNode<Self::Language> {
//!         &self.syntax
//!     }
//! }
//! ```
//!
//! # See Also
//!
//! - [rowan documentation](https://docs.rs/rowan) - The underlying CST library
//! - [`LosslessToken`](crate::LosslessToken) - For handling trivia in CSTs

use core::{cell::RefCell, marker::PhantomData};

use crate::{Logos, LosslessToken, Source, Tokenizer, chumsky};
use derive_more::{From, Into};
use rowan::{GreenNodeBuilder, Language, SyntaxNode};

/// A builder for constructing concrete syntax trees.
///
/// `SyntaxTreeBuilder` wraps rowan's [`GreenNodeBuilder`] and provides a convenient
/// interface for building syntax trees from tokens during parsing. The builder uses
/// interior mutability ([`RefCell`]) to allow sharing across parser combinators.
///
/// # Type Parameters
///
/// - `Lang`: The [`Language`] type that defines the syntax kinds for your language
///
/// # Usage Pattern
///
/// The typical usage pattern is:
///
/// 1. Create a builder with [`new()`](Self::new)
/// 2. Pass it to your parser implementation
/// 3. The parser calls [`start_node()`](Self::start_node), [`token()`](Self::token),
///    and [`finish_node()`](Self::finish_node) to build the tree
/// 4. Call [`finish()`](Self::finish) to get the final [`rowan::GreenNode`]
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::SyntaxTreeBuilder;
///
/// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
///
/// // Build a simple tree: Root(Identifier("hello"))
/// builder.start_node(SyntaxKind::Root);
/// builder.token(SyntaxKind::Identifier, "hello");
/// builder.finish_node();
///
/// let green_node = builder.finish();
/// ```
///
/// ## Using Checkpoints for Lookahead
///
/// Checkpoints allow you to start nodes retroactively, which is useful for
/// handling left-recursive or ambiguous grammars:
///
/// ```rust,ignore
/// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
/// let checkpoint = builder.checkpoint();
///
/// builder.token(SyntaxKind::Number, "42");
///
/// // Decide to wrap the number in a UnaryExpression
/// builder.start_node_at(checkpoint, SyntaxKind::UnaryExpression);
/// builder.token(SyntaxKind::Plus, "+");
/// builder.finish_node();
/// ```
///
/// # Interior Mutability
///
/// The builder uses [`RefCell`] internally, which means:
/// - It can be shared immutably across parser combinators
/// - Mutations are checked at runtime (will panic if you violate borrow rules)
/// - Typically safe in single-threaded parsing contexts
#[derive(Debug)]
pub struct SyntaxTreeBuilder<Lang> {
  builder: RefCell<GreenNodeBuilder<'static>>,
  _marker: PhantomData<Lang>,
}

impl<Lang> Default for SyntaxTreeBuilder<Lang>
where
  Lang: Language,
{
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<Lang> SyntaxTreeBuilder<Lang>
where
  Lang: Language,
{
  /// Creates a new empty syntax tree builder.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      builder: RefCell::new(GreenNodeBuilder::new()),
      _marker: PhantomData,
    }
  }

  /// Creates a checkpoint representing the current position in the tree.
  ///
  /// Checkpoints can be used with [`start_node_at()`](Self::start_node_at) to
  /// retroactively wrap already-added children in a new parent node. This is
  /// useful for handling left-recursive or ambiguous grammars.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  /// let checkpoint = builder.checkpoint();
  ///
  /// builder.token(SyntaxKind::Number, "42");
  ///
  /// // Wrap the number in an expression node
  /// builder.start_node_at(checkpoint, SyntaxKind::Expression);
  /// builder.finish_node();
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::checkpoint`]
  #[inline]
  pub fn checkpoint(&self) -> rowan::Checkpoint {
    self.builder.borrow().checkpoint()
  }

  /// Starts a new node with the given syntax kind.
  ///
  /// Must be paired with a corresponding [`finish_node()`](Self::finish_node) call.
  /// All tokens and child nodes added between `start_node()` and `finish_node()`
  /// will be children of this node.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  ///
  /// builder.start_node(SyntaxKind::BinaryExpression);
  /// builder.token(SyntaxKind::Number, "1");
  /// builder.token(SyntaxKind::Plus, "+");
  /// builder.token(SyntaxKind::Number, "2");
  /// builder.finish_node();
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::start_node`]
  #[inline]
  pub fn start_node(&self, kind: Lang::Kind)
  where
    Lang::Kind: Into<rowan::SyntaxKind>,
  {
    self.builder.borrow_mut().start_node(kind.into());
  }

  /// Starts a new node at a previously created checkpoint.
  ///
  /// This allows you to retroactively wrap children that were added after the
  /// checkpoint was created. Useful for handling operator precedence and
  /// left-recursive grammars.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  /// let checkpoint = builder.checkpoint();
  ///
  /// // Add a number
  /// builder.token(SyntaxKind::Number, "42");
  ///
  /// // Later, decide to wrap it in a unary expression
  /// builder.start_node_at(checkpoint, SyntaxKind::UnaryExpression);
  /// builder.token(SyntaxKind::Minus, "-");
  /// builder.finish_node();
  /// // Result: UnaryExpression(Number("42"), Minus("-"))
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::start_node_at`]
  #[inline]
  pub fn start_node_at(&self, checkpoint: rowan::Checkpoint, kind: Lang::Kind)
  where
    Lang::Kind: Into<rowan::SyntaxKind>,
  {
    self
      .builder
      .borrow_mut()
      .start_node_at(checkpoint, kind.into());
  }

  /// Adds a token with the given kind and text to the current node.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  ///
  /// builder.start_node(SyntaxKind::Identifier);
  /// builder.token(SyntaxKind::IdentifierToken, "my_variable");
  /// builder.finish_node();
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::token`]
  #[inline]
  pub fn token(&self, kind: Lang::Kind, text: &str)
  where
    Lang::Kind: Into<rowan::SyntaxKind>,
  {
    self.builder.borrow_mut().token(kind.into(), text);
  }

  /// Finishes the current node started with [`start_node()`](Self::start_node)
  /// or [`start_node_at()`](Self::start_node_at).
  ///
  /// # Panics
  ///
  /// Panics if there is no node to finish (i.e., `finish_node()` was called
  /// more times than `start_node()`).
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  ///
  /// builder.start_node(SyntaxKind::Root);
  /// builder.token(SyntaxKind::Identifier, "foo");
  /// builder.finish_node(); // Finishes the Root node
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::finish_node`]
  #[inline]
  pub fn finish_node(&self) {
    self.builder.borrow_mut().finish_node();
  }

  /// Completes the tree building and returns the final green node.
  ///
  /// This consumes the builder and returns the root [`rowan::GreenNode`],
  /// which can be converted to a [`rowan::SyntaxNode`] for traversal.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::SyntaxTreeBuilder;
  /// use rowan::SyntaxNode;
  ///
  /// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
  ///
  /// builder.start_node(SyntaxKind::Root);
  /// builder.token(SyntaxKind::Identifier, "foo");
  /// builder.finish_node();
  ///
  /// let green = builder.finish();
  /// let root = SyntaxNode::new_root(green);
  /// ```
  ///
  /// See also: [`rowan::GreenNodeBuilder::finish`]
  #[inline]
  pub fn finish(self) -> rowan::GreenNode {
    self.builder.into_inner().finish()
  }
}

/// A trait for types that can be parsed from a tokenizer and build CST nodes.
///
/// `Parseable` connects your CST node types with Chumsky parsers, allowing you to
/// build concrete syntax trees during parsing. The parser returns `()` as output,
/// but builds the tree via side effects through the [`SyntaxTreeBuilder`].
///
/// # Design
///
/// The `Parseable` trait is designed to:
/// - Work with any tokenizer implementing [`Tokenizer`]
/// - Integrate seamlessly with Chumsky's parser combinators
/// - Use side effects (via [`SyntaxTreeBuilder`]) to construct the CST
/// - Support lossless tokens via [`LosslessToken`] for preserving trivia
///
/// # Type Parameters
///
/// - `'a`: Lifetime of the input source
/// - `I`: The tokenizer type producing tokens
/// - `T`: The token type being parsed
/// - `Error`: The error type for parsing failures
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{Parseable, SyntaxTreeBuilder};
/// use logosky::{Tokenizer, LosslessToken, chumsky};
///
/// struct Expression;
///
/// impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Expression
/// where
///     I: Tokenizer<'a, T>,
///     T: LosslessToken<'a>,
/// {
///     type Language = MyLanguage;
///
///     fn parser<E>(
///         builder: &'a SyntaxTreeBuilder<Self::Language>,
///     ) -> impl chumsky::Parser<'a, I, (), E> + Clone
///     where
///         E: chumsky::extra::ParserExtra<'a, I, Error = Error>,
///     {
///         use chumsky::prelude::*;
///
///         // Start building an Expression node
///         just(TokenKind::Number).map(move |token| {
///             builder.start_node(SyntaxKind::Expression);
///             builder.token(SyntaxKind::Number, token.slice());
///             builder.finish_node();
///         })
///     }
/// }
/// ```
///
/// # Integration with Parsers
///
/// The typical workflow:
///
/// 1. Create a [`SyntaxTreeBuilder`]
/// 2. Call `YourType::parser(&builder)` to get a Chumsky parser
/// 3. Run the parser on your token stream
/// 4. Call `builder.finish()` to get the final CST
///
/// ```rust,ignore
/// let builder = SyntaxTreeBuilder::<MyLanguage>::new();
/// let parser = Expression::parser(&builder);
///
/// // Parse the input
/// parser.parse(tokens)?;
///
/// // Get the final CST
/// let green = builder.finish();
/// let root = SyntaxNode::new_root(green);
/// ```
pub trait Parseable<'a, I, T, Error> {
  /// The language of the syntax tree.
  type Language: Language;

  /// Returns a parser that can parse `Self` from the given tokenizer.
  ///
  /// The parser builds CST nodes as a side effect through the provided `builder`,
  /// and returns `()` as its output value.
  ///
  /// # Type Parameters
  ///
  /// - `E`: The parser extra context, providing error handling and state
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::{Parseable, SyntaxTreeBuilder};
  ///
  /// impl<'a, I, T, Error> Parseable<'a, I, T, Error> for Identifier {
  ///     type Language = MyLanguage;
  ///
  ///     fn parser<E>(
  ///         builder: &'a SyntaxTreeBuilder<Self::Language>,
  ///     ) -> impl chumsky::Parser<'a, I, (), E> + Clone
  ///     where
  ///         E: chumsky::extra::ParserExtra<'a, I, Error = Error>,
  ///     {
  ///         // Implementation that builds an Identifier node
  ///         todo!()
  ///     }
  /// }
  /// ```
  fn parser<E>(
    builder: &'a SyntaxTreeBuilder<Self::Language>,
  ) -> impl chumsky::Parser<'a, I, (), E> + Clone
  where
    I: Tokenizer<'a, T, Slice = <<T::Logos as Logos<'a>>::Source as Source>::Slice<'a>>,
    T: LosslessToken<'a>,
    <T::Logos as Logos<'a>>::Source: Source<Slice<'a> = &'a str>,
    Error: 'a,
    E: chumsky::extra::ParserExtra<'a, I, Error = Error> + 'a;
}

/// The main trait for typed CST nodes with zero-cost conversions.
///
/// `Node` provides a type-safe wrapper around rowan's untyped [`SyntaxNode`], allowing
/// you to work with strongly-typed CST nodes. The conversion between typed and untyped
/// nodes has **zero runtime cost** - both representations have exactly the same memory
/// layout (a pointer to the tree root and a pointer to the node itself).
///
/// # Design
///
/// The `Node` trait enables:
/// - **Type safety**: Compile-time guarantees about node types
/// - **Zero-cost**: No runtime overhead for typed wrappers
/// - **Pattern matching**: Cast nodes to specific types
/// - **Tree traversal**: Navigate the CST with type information
///
/// # Type Parameters
///
/// - `Language`: The rowan [`Language`] type defining syntax kinds
///
/// # Implementation
///
/// To implement `Node`, you need to:
/// 1. Define a struct wrapping [`SyntaxNode<Language>`](SyntaxNode)
/// 2. Specify the [`KIND`](Self::KIND) constant
/// 3. Implement [`can_cast()`](Self::can_cast) to check if a kind matches
/// 4. Implement [`try_cast()`](Self::try_cast) to convert from untyped nodes
/// 5. Implement [`syntax()`](Self::syntax) to access the underlying node
///
/// # Examples
///
/// ## Basic Node Implementation
///
/// ```rust,ignore
/// use logosky::cst::{Node, error};
/// use rowan::SyntaxNode;
///
/// #[derive(Debug, Clone)]
/// struct IdentifierNode {
///     syntax: SyntaxNode<MyLanguage>,
/// }
///
/// impl Node for IdentifierNode {
///     type Language = MyLanguage;
///     const KIND: SyntaxKind = SyntaxKind::Identifier;
///
///     fn can_cast(kind: SyntaxKind) -> bool {
///         kind == Self::KIND
///     }
///
///     fn try_cast(
///         syntax: SyntaxNode<Self::Language>
///     ) -> Result<Self, error::SyntaxNodeMismatch<Self>> {
///         if Self::can_cast(syntax.kind()) {
///             Ok(Self { syntax })
///         } else {
///             Err(error::SyntaxNodeMismatch::new(Self::KIND, syntax))
///         }
///     }
///
///     fn syntax(&self) -> &SyntaxNode<Self::Language> {
///         &self.syntax
///     }
/// }
/// ```
///
/// ## Using Nodes
///
/// ```rust,ignore
/// use logosky::cst::Node;
///
/// // Try to cast an untyped node
/// let identifier = IdentifierNode::try_cast(syntax_node)?;
///
/// // Access the source text
/// let text = identifier.source_string();
///
/// // Clone for mutation
/// let mutable = identifier.clone_for_update();
/// ```
///
/// ## Enum Nodes for Variants
///
/// ```rust,ignore
/// use logosky::cst::Node;
///
/// #[derive(Debug, Clone)]
/// enum Expression {
///     Binary(BinaryExpr),
///     Unary(UnaryExpr),
///     Literal(LiteralExpr),
/// }
///
/// impl Node for Expression {
///     type Language = MyLanguage;
///     const KIND: SyntaxKind = SyntaxKind::Expression; // Marker, not used
///
///     fn can_cast(kind: SyntaxKind) -> bool {
///         matches!(
///             kind,
///             SyntaxKind::BinaryExpr | SyntaxKind::UnaryExpr | SyntaxKind::Literal
///         )
///     }
///
///     fn try_cast(
///         syntax: SyntaxNode<Self::Language>
///     ) -> Result<Self, error::SyntaxNodeMismatch<Self>> {
///         match syntax.kind() {
///             SyntaxKind::BinaryExpr => Ok(Expression::Binary(BinaryExpr { syntax })),
///             SyntaxKind::UnaryExpr => Ok(Expression::Unary(UnaryExpr { syntax })),
///             SyntaxKind::Literal => Ok(Expression::Literal(LiteralExpr { syntax })),
///             _ => Err(error::SyntaxNodeMismatch::new(Self::KIND, syntax)),
///         }
///     }
///
///     fn syntax(&self) -> &SyntaxNode<Self::Language> {
///         match self {
///             Expression::Binary(e) => &e.syntax,
///             Expression::Unary(e) => &e.syntax,
///             Expression::Literal(e) => &e.syntax,
///         }
///     }
/// }
/// ```
pub trait Node: core::fmt::Debug {
  /// The language of the syntax tree.
  type Language: Language;

  /// The syntax kind of this CST node.
  ///
  /// For enum nodes representing multiple variants, this can be a marker value.
  const KIND: <Self::Language as Language>::Kind;

  /// Returns `true` if the given kind can be cast to this CST node.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// // Simple node: only one kind
  /// impl Node for IdentifierNode {
  ///     fn can_cast(kind: SyntaxKind) -> bool {
  ///         kind == SyntaxKind::Identifier
  ///     }
  ///     // ...
  /// }
  ///
  /// // Enum node: multiple kinds
  /// impl Node for Expression {
  ///     fn can_cast(kind: SyntaxKind) -> bool {
  ///         matches!(kind, SyntaxKind::BinaryExpr | SyntaxKind::UnaryExpr)
  ///     }
  ///     // ...
  /// }
  /// ```
  fn can_cast(kind: <Self::Language as Language>::Kind) -> bool
  where
    Self: Sized;

  /// Attempts to cast the given syntax node to this CST node.
  ///
  /// Returns an error if the node's kind doesn't match this type.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// let identifier = IdentifierNode::try_cast(syntax_node)?;
  /// ```
  fn try_cast(syntax: SyntaxNode<Self::Language>) -> Result<Self, error::SyntaxNodeMismatch<Self>>
  where
    Self: Sized;

  /// Returns a reference to the underlying syntax node.
  ///
  /// This provides access to rowan's tree traversal APIs.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// let node: IdentifierNode = ...;
  /// let parent = node.syntax().parent();
  /// let children = node.syntax().children();
  /// ```
  fn syntax(&self) -> &SyntaxNode<Self::Language>;

  /// Returns the source string of this CST node.
  ///
  /// This includes all text spanned by this node, including whitespace and trivia.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// let identifier: IdentifierNode = ...;
  /// assert_eq!(identifier.source_string(), "my_variable");
  /// ```
  fn source_string(&self) -> String {
    self.syntax().to_string()
  }

  /// Clones this CST node for update operations.
  ///
  /// This creates a mutable copy of the node that can be modified using rowan's
  /// mutation APIs. The original tree remains unchanged.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// let original: IdentifierNode = ...;
  /// let mut mutable = original.clone_for_update();
  ///
  /// // Modify the mutable copy
  /// // (using rowan's mutation APIs)
  /// ```
  fn clone_for_update(&self) -> Self
  where
    Self: Sized,
  {
    Self::try_cast(self.syntax().clone_for_update()).unwrap()
  }

  /// Clones the subtree rooted at this CST node.
  ///
  /// This creates a deep copy of this node and all its descendants, detached
  /// from the original tree.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::Node;
  ///
  /// let original: ExpressionNode = ...;
  /// let copy = original.clone_subtree();
  ///
  /// // copy is independent of original
  /// ```
  fn clone_subtree(&self) -> Self
  where
    Self: Sized,
  {
    Self::try_cast(self.syntax().clone_subtree()).unwrap()
  }
}

/// An iterator over typed CST children of a particular node type.
///
/// `SyntaxNodeChildren` filters and casts child nodes to a specific typed node type,
/// skipping any children that cannot be cast to the target type.
///
/// # Type Parameters
///
/// - `N`: The typed [`Node`] type to iterate over
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{Node, cast};
///
/// // Get all Identifier children of a function
/// let identifiers: Vec<IdentifierNode> = cast::children(&function_node.syntax())
///     .collect();
///
/// // Filter by kind within the same type
/// let params = cast::children::<Parameter>(&function_node.syntax())
///     .by_kind(|k| k == SyntaxKind::Parameter);
/// ```
#[derive(Debug, Clone, From, Into)]
#[repr(transparent)]
pub struct SyntaxNodeChildren<N: Node> {
  inner: rowan::SyntaxNodeChildren<N::Language>,
}

impl<N: Node> SyntaxNodeChildren<N> {
  #[inline]
  fn new(parent: &SyntaxNode<N::Language>) -> Self {
    Self {
      inner: parent.children(),
    }
  }

  /// Returns an iterator over syntax node children matching a kind predicate.
  ///
  /// This allows further filtering of children based on their syntax kind,
  /// returning the underlying [`SyntaxNode`] instead of typed nodes.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::cast;
  ///
  /// // Get all expression children, filtered by specific kinds
  /// let binary_exprs = cast::children::<Expression>(&node)
  ///     .by_kind(|k| k == SyntaxKind::BinaryExpr);
  /// ```
  pub fn by_kind<F>(self, f: F) -> impl Iterator<Item = SyntaxNode<N::Language>>
  where
    F: Fn(<N::Language as Language>::Kind) -> bool,
  {
    self.inner.by_kind(f)
  }
}

impl<N: Node> Iterator for SyntaxNodeChildren<N> {
  type Item = N;

  #[inline]
  fn next(&mut self) -> Option<N> {
    self.inner.find_map(|t| N::try_cast(t).ok())
  }
}

/// Utility functions for casting and accessing CST nodes.
///
/// This module provides convenient functions for working with typed CST nodes,
/// including finding children, accessing tokens, and casting between types.
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::cast;
///
/// // Get the first identifier child
/// let identifier = cast::child::<IdentifierNode>(&parent_node);
///
/// // Get all statement children
/// let statements: Vec<Statement> = cast::children(&function_node).collect();
///
/// // Get a specific token
/// let equals_token = cast::token(&assignment_node, &SyntaxKind::Equals);
/// ```
pub mod cast {
  use super::{Language, Node, SyntaxNode, SyntaxNodeChildren};

  /// Returns the first child of a specific typed node type.
  ///
  /// Searches through the children of the parent node and returns the first child
  /// that can be successfully cast to the specified node type `N`.
  ///
  /// # Type Parameters
  ///
  /// - `N`: The typed [`Node`] type to search for
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::cast;
  ///
  /// // Find the first identifier child
  /// if let Some(identifier) = cast::child::<IdentifierNode>(&function_syntax) {
  ///     println!("Function name: {}", identifier.source_string());
  /// }
  ///
  /// // Find the first expression in a statement
  /// let expr = cast::child::<Expression>(&statement_syntax)?;
  /// ```
  #[inline]
  pub fn child<N: Node>(parent: &SyntaxNode<N::Language>) -> Option<N> {
    parent.children().find_map(|t| N::try_cast(t).ok())
  }

  /// Returns an iterator over all children of a specific typed node type.
  ///
  /// Iterates through all children of the parent node, yielding only those that
  /// can be successfully cast to the specified node type `N`.
  ///
  /// # Type Parameters
  ///
  /// - `N`: The typed [`Node`] type to iterate over
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::cast;
  ///
  /// // Get all parameters of a function
  /// let parameters: Vec<Parameter> = cast::children(&function_syntax).collect();
  ///
  /// // Count the number of statements in a block
  /// let statement_count = cast::children::<Statement>(&block_syntax).count();
  ///
  /// // Find the first parameter with a specific name
  /// let param = cast::children::<Parameter>(&function_syntax)
  ///     .find(|p| p.name() == "self");
  /// ```
  #[inline]
  pub fn children<N: Node>(parent: &SyntaxNode<N::Language>) -> SyntaxNodeChildren<N> {
    SyntaxNodeChildren::new(parent)
  }

  /// Returns the first token child with the specified syntax kind.
  ///
  /// Searches through all tokens (not nodes) that are direct children of the parent
  /// and returns the first one matching the specified kind.
  ///
  /// # Type Parameters
  ///
  /// - `L`: The [`Language`] type defining syntax kinds
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::cast;
  ///
  /// // Get the equals token from an assignment
  /// let equals = cast::token(&assignment_node, &SyntaxKind::Equals)?;
  ///
  /// // Get the opening parenthesis of a function call
  /// let lparen = cast::token(&call_node, &SyntaxKind::LeftParen)?;
  ///
  /// // Check if a node has a specific keyword
  /// if let Some(async_kw) = cast::token(&function_node, &SyntaxKind::AsyncKeyword) {
  ///     println!("Function is async");
  /// }
  /// ```
  #[inline]
  pub fn token<L: Language>(
    parent: &SyntaxNode<L>,
    kind: &L::Kind,
  ) -> Option<rowan::SyntaxToken<L>> {
    parent
      .children_with_tokens()
      .by_kind(|k| k.eq(kind))
      .filter_map(|it| it.into_token())
      .next()
  }
}

/// Error types for CST operations.
///
/// This module provides error types that can occur when working with CST nodes,
/// primarily around type casting and node validation.
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{Node, error};
///
/// match IdentifierNode::try_cast(syntax_node) {
///     Ok(identifier) => println!("Got identifier: {}", identifier.source_string()),
///     Err(mismatch) => {
///         eprintln!("Expected {:?}, but found {:?}",
///             mismatch.expected(),
///             mismatch.found().kind());
///     }
/// }
/// ```
pub mod error {
  use super::{Language, Node};
  use rowan::SyntaxNode;

  /// An error indicating a mismatch between expected and actual syntax node kinds.
  ///
  /// This error occurs when attempting to cast a [`SyntaxNode`] to a typed [`Node`]
  /// type, but the node's kind doesn't match the expected kind for that type.
  ///
  /// # Type Parameters
  ///
  /// - `N`: The typed [`Node`] type that was expected
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::{Node, error};
  ///
  /// let result = IdentifierNode::try_cast(syntax_node);
  ///
  /// match result {
  ///     Ok(identifier) => {
  ///         // Successfully cast
  ///         println!("Identifier: {}", identifier.source_string());
  ///     }
  ///     Err(mismatch) => {
  ///         // Cast failed
  ///         eprintln!("Type mismatch: {}", mismatch);
  ///         eprintln!("Expected: {:?}", mismatch.expected());
  ///         eprintln!("Found: {:?}", mismatch.found().kind());
  ///     }
  /// }
  /// ```
  ///
  /// ## Recovering from Errors
  ///
  /// ```rust,ignore
  /// use logosky::cst::error::SyntaxNodeMismatch;
  ///
  /// let result = Expression::try_cast(syntax_node);
  ///
  /// let node = match result {
  ///     Ok(expr) => expr,
  ///     Err(mismatch) => {
  ///         // Recover the original syntax node
  ///         let (expected_kind, original_node) = mismatch.into_components();
  ///         // Try a different type
  ///         Statement::try_cast(original_node)?
  ///     }
  /// };
  /// ```
  #[derive(Debug, Clone, PartialEq, Eq, Hash, derive_more::Display)]
  #[display(
    "syntax node mismatch: expected syntax node of kind {}, but found syntax node of kind {}",
    expected,
    found.kind()
  )]
  pub struct SyntaxNodeMismatch<N: Node> {
    expected: <N::Language as Language>::Kind,
    found: SyntaxNode<N::Language>,
  }

  impl<N> core::error::Error for SyntaxNodeMismatch<N>
  where
    N: Node + core::fmt::Debug,
    <N::Language as Language>::Kind: core::fmt::Display,
  {
  }

  impl<N: Node> SyntaxNodeMismatch<N> {
    /// Creates a new syntax node mismatch error.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use logosky::cst::error::SyntaxNodeMismatch;
    ///
    /// let error = SyntaxNodeMismatch::new(
    ///     SyntaxKind::Identifier,
    ///     syntax_node
    /// );
    /// ```
    #[inline]
    pub const fn new(
      expected: <N::Language as Language>::Kind,
      found: SyntaxNode<N::Language>,
    ) -> Self {
      Self { expected, found }
    }

    /// Returns the expected syntax node kind.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use logosky::cst::Node;
    ///
    /// if let Err(mismatch) = IdentifierNode::try_cast(node) {
    ///     println!("Expected kind: {:?}", mismatch.expected());
    /// }
    /// ```
    #[inline]
    pub const fn expected(&self) -> &<N::Language as Language>::Kind {
      &self.expected
    }

    /// Returns a reference to the syntax node that was found.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use logosky::cst::Node;
    ///
    /// if let Err(mismatch) = IdentifierNode::try_cast(node) {
    ///     println!("Found kind: {:?}", mismatch.found().kind());
    ///     println!("Found text: {}", mismatch.found().text());
    /// }
    /// ```
    #[inline]
    pub const fn found(&self) -> &SyntaxNode<N::Language> {
      &self.found
    }

    /// Consumes the error and returns the expected kind and found node.
    ///
    /// This is useful for recovering the original syntax node after a failed cast,
    /// allowing you to try casting to a different type.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use logosky::cst::Node;
    ///
    /// let result = IdentifierNode::try_cast(syntax_node);
    ///
    /// if let Err(mismatch) = result {
    ///     let (expected, node) = mismatch.into_components();
    ///     // Try casting to a different type
    ///     let keyword = KeywordNode::try_cast(node)?;
    /// }
    /// ```
    #[inline]
    pub fn into_components(self) -> (<N::Language as Language>::Kind, SyntaxNode<N::Language>) {
      (self.expected, self.found)
    }
  }
}
