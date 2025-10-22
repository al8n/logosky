pub use incomplete::*;
pub use node_mismatch::*;
pub use token_mismatch::*;

use super::CstElement;
use derive_more::{IsVariant, Unwrap, TryUnwrap};

mod incomplete;
mod node_mismatch;
mod token_mismatch;

/// Error type for CST node casting operations.
///
/// This error can occur when attempting to cast an untyped `SyntaxNode` to a typed
/// [`CstNode`](crate::cst::CstNode). It encompasses two kinds of failures:
///
/// - **Mismatch**: The node's kind doesn't match the expected type
/// - **IncompleteSyntax**: The node is missing required child components
///
/// # Type Parameters
///
/// - `E`: The CST element type being cast to
/// - `N`: A `typenum` unsigned integer representing the number of missing components
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{CstNode, error::CastNodeError};
/// use typenum::U2;
///
/// match MyNode::try_cast_node(syntax_node) {
///     Ok(node) => { /* success */ }
///     Err(CastNodeError::<MyNode, U2>::Mismatch(e)) => {
///         eprintln!("Wrong node type: {}", e);
///     }
///     Err(CastNodeError::<MyNode, U2>::IncompleteSyntax(e)) => {
///         eprintln!("Missing components: {}", e);
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, thiserror::Error)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum CastNodeError<E: CstElement> {
  /// The syntax node's kind doesn't match the expected CST node type.
  #[error(transparent)]
  Mismatch(#[from] CstNodeMismatch<E>),
  /// The syntax node is incomplete and missing required child components.
  #[error(transparent)]
  IncompleteSyntax(#[from] IncompleteSyntax<E>),
}

/// Error type for CST token casting operations.
///
/// This error can occur when attempting to cast an untyped `SyntaxToken` to a typed
/// [`CstToken`](crate::cst::CstToken). It encompasses two kinds of failures:
///
/// - **Mismatch**: The token's kind doesn't match the expected type
/// - **IncompleteSyntax**: The token context is missing required components
///
/// # Type Parameters
///
/// - `E`: The CST element type being cast to
/// - `N`: A `typenum` unsigned integer representing the number of missing components
///
/// # Examples
///
/// ```rust,ignore
/// use logosky::cst::{CstToken, error::CastTokenError};
/// use typenum::U1;
///
/// match MyToken::try_cast_token(syntax_token) {
///     Ok(token) => { /* success */ }
///     Err(CastTokenError::<MyToken, U1>::Mismatch(e)) => {
///         eprintln!("Wrong token type: {}", e);
///     }
///     Err(CastTokenError::<MyToken, U1>::IncompleteSyntax(e)) => {
///         eprintln!("Missing components: {}", e);
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, IsVariant, Unwrap, TryUnwrap, thiserror::Error)]
#[unwrap(ref, ref_mut)]
#[try_unwrap(ref, ref_mut)]
pub enum CastTokenError<E: CstElement> {
  /// The syntax token's kind doesn't match the expected CST token type.
  #[error(transparent)]
  Mismatch(#[from] CstTokenMismatch<E>),
  /// The syntax token context is incomplete and missing required components.
  #[error(transparent)]
  IncompleteSyntax(#[from] IncompleteSyntax<E>),
}
