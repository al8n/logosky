//! Const-generic based syntax and incomplete syntax error implementation.
//!
//! This implementation uses const generics to specify the number of components
//! at compile time using a `const COMPONENTS: usize` associated constant.

use crate::utils::{GenericVec, syntax::Syntax};
use core::{
  fmt::{Debug, Display},
  hash::Hash,
};

/// Represents an incomplete syntax with missing components.
///
/// This error type is used to track which components are missing from a syntax
/// construct during parsing. It stores components as a set (no duplicates) and
/// always contains at least one missing component.
///
/// Internally uses [`GenericVec`] for efficient stack-based storage.
///
/// # Design Philosophy
///
/// When parsing fails, it's valuable to report *all* missing components rather
/// than just the first one encountered. This type accumulates missing components
/// up to the syntax's maximum component count.
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use logosky::utils::syntax::{Syntax, IncompleteSyntax};
/// use core::fmt;
///
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// enum IfStatementComponent {
///     IfKeyword,
///     Condition,
///     ThenBlock,
/// }
///
/// impl fmt::Display for IfStatementComponent {
///     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         match self {
///             Self::IfKeyword => write!(f, "'if' keyword"),
///             Self::Condition => write!(f, "condition"),
///             Self::ThenBlock => write!(f, "then block"),
///         }
///     }
/// }
///
/// struct IfStatement;
///
/// impl Syntax for IfStatement {
///     type Component = IfStatementComponent;
///     const COMPONENTS: usize = 3;
///
///     fn possible_components() -> [Self::Component; 3] {
///         [
///             IfStatementComponent::IfKeyword,
///             IfStatementComponent::Condition,
///             IfStatementComponent::ThenBlock,
///         ]
///     }
/// }
///
/// // Report a missing component
/// let error = IncompleteSyntax::<IfStatement>::new(
///     IfStatementComponent::Condition
/// );
/// assert_eq!(error.len(), 1);
///
/// // Add more missing components
/// let mut error = error;
/// error.push(IfStatementComponent::ThenBlock);
/// assert_eq!(error.len(), 2);
/// ```
///
/// ## Error Message Formatting
///
/// ```rust
/// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
/// # use core::fmt;
/// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// # enum Component { A, B }
/// # impl fmt::Display for Component {
/// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
/// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
/// #     }
/// # }
/// # struct MySyntax;
/// # impl Syntax for MySyntax {
/// #     type Component = Component;
/// #     const COMPONENTS: usize = 2;
/// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
/// # }
/// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
/// assert_eq!(format!("{}", error), "incomplete syntax: component A is missing");
///
/// error.push(Component::B);
/// assert_eq!(format!("{}", error), "incomplete syntax: components A, B are missing");
/// ```
#[derive(Debug, Clone)]
pub struct IncompleteSyntax<S: Syntax> {
  components: GenericVec<S::Component, { S::COMPONENTS }>,
}

impl<S> PartialEq for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    self.components == other.components
  }
}

impl<S> Eq for IncompleteSyntax<S> where S: Syntax {}

impl<S> Hash for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.components.hash(state);
  }
}

impl<S> AsRef<[S::Component]> for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[S::Component] {
    self.components.as_slice()
  }
}

impl<S> AsMut<[S::Component]> for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_mut(&mut self) -> &mut [S::Component] {
    self.components.as_mut_slice()
  }
}

impl<S> IncompleteSyntax<S>
where
  S: Syntax,
{
  /// Creates a new incomplete syntax error with the specified missing component.
  ///
  /// The error always starts with at least one missing component.
  ///
  /// # Panics
  ///
  /// Panics if `S::COMPONENTS` is 0 (which would be a malformed Syntax implementation).
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "A") }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 1;
  /// #     fn possible_components() -> [Self::Component; 1] { [Component::A] }
  /// # }
  /// let error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// assert_eq!(error.len(), 1);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(component: S::Component) -> Self {
    if S::COMPONENTS == 0 {
      panic!("IncompleteSyntax requires S::COMPONENTS to be non-zero");
    }

    let mut components = GenericVec::new();
    components.push(component);

    Self { components }
  }

  /// Tries to create an incomplete syntax error from an iterator of components.
  ///
  /// Returns `None` if:
  /// - The iterator yields no components
  /// - The iterator yields more unique components than the buffer can hold
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let components = vec![Component::A, Component::B];
  /// let error = IncompleteSyntax::<MySyntax>::from_iter(components).unwrap();
  /// assert_eq!(error.len(), 2);
  ///
  /// // Empty iterator returns None
  /// let error = IncompleteSyntax::<MySyntax>::from_iter(std::iter::empty());
  /// assert!(error.is_none());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[allow(clippy::should_implement_trait)]
  pub fn from_iter(iter: impl IntoIterator<Item = S::Component>) -> Option<Self> {
    let mut components = GenericVec::new();
    for component in iter {
      if Self::try_push_impl(&mut components, component).is_some() {
        return None; // Overflow
      }
    }
    (!components.is_empty()).then_some(Self { components })
  }

  // Helper function for deduplication logic
  fn try_push_impl(
    components: &mut GenericVec<S::Component, { S::COMPONENTS }>,
    component: S::Component,
  ) -> Option<S::Component> {
    // Check for duplicates - if already present, treat as success
    if components.as_slice().contains(&component) {
      return None;
    }

    components.try_push(component).err()
  }

  /// Returns the number of missing components.
  ///
  /// The length is always at least 1.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// assert_eq!(error.len(), 1);
  /// error.push(Component::B);
  /// assert_eq!(error.len(), 2);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[allow(clippy::len_without_is_empty)]
  pub const fn len(&self) -> usize {
    self.components.len()
  }

  /// Returns the maximum number of components this error can hold.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B, C }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "X") }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 3;
  /// #     fn possible_components() -> [Self::Component; 3] {
  /// #         [Component::A, Component::B, Component::C]
  /// #     }
  /// # }
  /// let error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// assert_eq!(error.capacity(), 3);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn capacity(&self) -> usize {
    self.components.capacity()
  }

  /// Returns `true` if the error is at full capacity.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// assert!(!error.is_full());
  /// error.push(Component::B);
  /// assert!(error.is_full());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.components.is_full()
  }

  /// Pushes a new missing component into the error.
  ///
  /// If the component already exists in the error, this is a no-op (silently succeeds).
  /// This maintains the set semantics where each component appears at most once.
  ///
  /// # Panics
  ///
  /// Panics if the error is already full and the component is not already present.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// error.push(Component::B);
  /// // Pushing the same component again is a no-op
  /// error.push(Component::A);
  /// assert_eq!(error.len(), 2);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn push(&mut self, component: S::Component) {
    if Self::try_push_impl(&mut self.components, component).is_some() {
      panic!("IncompleteSyntax buffer overflow: cannot push more components")
    }
  }

  /// Tries to push a new missing component into the error.
  ///
  /// Returns:
  /// - `None` if the component was added or already exists (success)
  /// - `Some(component)` if the buffer is full and the component is not present (failure)
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B, C }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "X") }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// assert!(error.try_push(Component::B).is_none()); // Success
  /// assert_eq!(error.try_push(Component::C), Some(Component::C)); // Full!
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn try_push(&mut self, component: S::Component) -> Option<S::Component> {
    Self::try_push_impl(&mut self.components, component)
  }

  /// Returns a slice of the missing components.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// error.push(Component::B);
  /// assert_eq!(error.as_slice(), &[Component::A, Component::B]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_slice(&self) -> &[S::Component] {
    self.components.as_slice()
  }

  /// Returns a mutable slice of the missing components.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// error.as_mut_slice()[0] = Component::B;
  /// assert_eq!(error.as_slice()[0], Component::B);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_slice(&mut self) -> &mut [S::Component] {
    self.components.as_mut_slice()
  }

  /// Returns an iterator over the missing components.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # use logosky::utils::syntax::{Syntax, IncompleteSyntax};
  /// # use core::fmt;
  /// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  /// # enum Component { A, B }
  /// # impl fmt::Display for Component {
  /// #     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  /// #         match self { Self::A => write!(f, "A"), Self::B => write!(f, "B") }
  /// #     }
  /// # }
  /// # struct MySyntax;
  /// # impl Syntax for MySyntax {
  /// #     type Component = Component;
  /// #     const COMPONENTS: usize = 2;
  /// #     fn possible_components() -> [Self::Component; 2] { [Component::A, Component::B] }
  /// # }
  /// let mut error = IncompleteSyntax::<MySyntax>::new(Component::A);
  /// error.push(Component::B);
  /// let collected: Vec<_> = error.iter().collect();
  /// assert_eq!(collected, vec![&Component::A, &Component::B]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter(&self) -> core::slice::Iter<'_, S::Component> {
    self.components.iter()
  }
}

impl<S> Display for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let components = self.as_slice();

    if components.len() == 1 {
      write!(
        f,
        "incomplete syntax: component {} is missing",
        components[0]
      )
    } else {
      write!(f, "incomplete syntax: components ")?;
      for (i, component) in components.iter().enumerate() {
        if i > 0 {
          write!(f, ", ")?;
        }
        write!(f, "{}", component)?;
      }
      write!(f, " are missing")
    }
  }
}

impl<S> core::error::Error for IncompleteSyntax<S> where S: Syntax + Debug {}
