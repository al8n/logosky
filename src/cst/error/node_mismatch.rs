use super::super::{Language, CstNode};
use rowan::SyntaxNode;

/// An error indicating a mismatch between expected and actual syntax node kinds.
///
/// This error occurs when attempting to cast a [`SyntaxNode`] to a typed [`Node`]
/// type, but the node's kind doesn't match the expected kind for that type.
///
/// # Type Parameters
///
/// - `N`: The typed [`CstNode`] type that was expected
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{CstNode, error};
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
/// use logosky::cst::error::CstNodeMismatch;
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
pub struct CstNodeMismatch<N: CstNode> {
  expected: <N::Language as Language>::Kind,
  found: SyntaxNode<N::Language>,
}

impl<N> core::error::Error for CstNodeMismatch<N>
where
  N: CstNode + core::fmt::Debug,
  <N::Language as Language>::Kind: core::fmt::Display,
{
}

impl<N: CstNode> CstNodeMismatch<N> {
  /// Creates a new syntax node mismatch error.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::cst::error::CstNodeMismatch;
  ///
  /// let error = CstNodeMismatch::new(
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
  /// use logosky::cst::CstNode;
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
  /// use logosky::cst::CstNode;
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
