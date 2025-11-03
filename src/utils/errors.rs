//! Error collection container that adapts to allocation environments.
//!
//! This module provides the `Errors` type for collecting multiple errors during parsing
//! or validation. The container automatically adapts based on available features:
//!
//! - **no_std (no alloc)**: Uses `GenericVec<E, 2>` with fixed capacity of 2 errors
//! - **alloc/std**: Uses `Vec<E>` for unlimited error collection
//!
//! # Examples
//!
//! ## Basic Usage
//!
//! ```rust
//! use logosky::utils::Errors;
//!
//! let mut errors = Errors::new();
//! errors.push("First error");
//! errors.push("Second error");
//!
//! assert_eq!(errors.len(), 2);
//! assert!(!errors.is_empty());
//! ```
//!
//! ## Iteration
//!
//! ```rust
//! use logosky::utils::Errors;
//!
//! let mut errors = Errors::new();
//! errors.push(1);
//! errors.push(2);
//!
//! let sum: i32 = errors.iter().sum();
//! assert_eq!(sum, 3);
//! ```

use core::fmt::{Debug, Display};

#[cfg(any(feature = "alloc", feature = "std"))]
use std::vec::Vec;

#[cfg(not(any(feature = "alloc", feature = "std")))]
use crate::utils::GenericVec;

/// Default error container for no-alloc environments.
///
/// Uses a stack-allocated `GenericVec` with capacity for 2 errors.
/// When the capacity is exceeded, additional errors are silently dropped.
#[cfg(all(
  not(any(feature = "alloc", feature = "std")),
  feature = "generic-array"
))]
pub type DefaultContainer<E> = GenericVec<E, super::typenum::U2>;

/// Default error container for no-alloc environments.
///
/// Uses a stack-allocated `GenericVec` with capacity for 2 errors.
/// When the capacity is exceeded, additional errors are silently dropped.
#[cfg(all(
  not(any(feature = "alloc", feature = "std")),
  not(feature = "generic-array")
))]
pub type DefaultContainer<E> = GenericVec<E, 2>;

/// Default error container for alloc/std environments.
///
/// Uses a heap-allocated `Vec` for unlimited error collection.
#[cfg(any(feature = "alloc", feature = "std"))]
pub type DefaultContainer<E> = Vec<E>;

/// A collection of errors that adapts to the allocation environment.
///
/// This type is generic over both the error type `E` and the container `C`.
/// By default:
/// - In no-alloc environments: Uses `GenericVec<E, 2>` (capacity of 2)
/// - In alloc/std environments: Uses `Vec<E>` (unlimited capacity)
///
/// # Type Parameters
///
/// - `E`: The error type to store
/// - `C`: The container type (defaults to environment-appropriate container)
///
/// # Examples
///
/// ## Using Default Container
///
/// ```rust
/// use logosky::utils::Errors;
///
/// let mut errors = Errors::new();
/// errors.push("Error 1");
/// errors.push("Error 2");
///
/// assert_eq!(errors.len(), 2);
/// ```
///
/// ## Type Inference
///
/// ```rust
/// use logosky::utils::Errors;
///
/// // Type inference works seamlessly
/// let mut errors = Errors::new();
/// errors.push("Error 1");
/// errors.push("Error 2");
///
/// let first: Option<&&str> = errors.first();
/// assert_eq!(first, Some(&"Error 1"));
/// ```
#[derive(
  Debug,
  Clone,
  PartialEq,
  Eq,
  Hash,
  derive_more::Deref,
  derive_more::DerefMut,
  derive_more::AsRef,
  derive_more::AsMut,
)]
pub struct Errors<E, C = DefaultContainer<E>> {
  #[deref]
  #[deref_mut]
  #[as_ref]
  #[as_mut]
  container: C,
  _phantom: core::marker::PhantomData<E>,
}

// Implementation for no-alloc environments (GenericVec)
#[cfg(not(any(feature = "alloc", feature = "std")))]
impl<E> Errors<E> {
  /// Creates a new empty error collection.
  ///
  /// In no-alloc environments, this creates a `GenericVec` with capacity 2.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let errors: Errors<String> = Errors::new();
  /// assert!(errors.is_empty());
  /// ```
  #[inline]
  #[cfg(not(feature = "generic-array"))]
  pub const fn new() -> Self {
    Self::new_in(GenericVec::new())
  }

  /// Creates a new empty error collection.
  ///
  /// In no-alloc environments, this creates a `GenericVec` with capacity 2.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let errors: Errors<String> = Errors::new();
  /// assert!(errors.is_empty());
  /// ```
  #[inline]
  #[cfg(feature = "generic-array")]
  pub fn new() -> Self {
    Self::new_in(GenericVec::new())
  }
}

// Implementation for alloc/std environments (Vec)
#[cfg(any(feature = "alloc", feature = "std"))]
impl<E> Errors<E> {
  /// Creates a new empty error collection.
  ///
  /// In alloc/std environments, this creates an empty `Vec`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let errors: Errors<String> = Errors::new();
  /// assert!(errors.is_empty());
  /// ```
  #[inline]
  pub const fn new() -> Self {
    Self::new_in(Vec::new())
  }

  /// Creates a new error collection with the specified capacity.
  ///
  /// This pre-allocates space for `capacity` errors.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let errors: Errors<String> = Errors::with_capacity(10);
  /// assert_eq!(errors.capacity(), 10);
  /// ```
  #[inline]
  pub fn with_capacity(capacity: usize) -> Self {
    Self {
      container: Vec::with_capacity(capacity),
      _phantom: core::marker::PhantomData,
    }
  }

  /// Returns the number of errors the collection can hold without reallocating.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let errors: Errors<String> = Errors::with_capacity(10);
  /// assert_eq!(errors.capacity(), 10);
  /// ```
  #[inline]
  pub fn capacity(&self) -> usize {
    self.container.capacity()
  }

  /// Reserves capacity for at least `additional` more errors.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::Errors;
  ///
  /// let mut errors: Errors<String> = Errors::new();
  /// errors.reserve(10);
  /// assert!(errors.capacity() >= 10);
  /// ```
  #[inline]
  pub fn reserve(&mut self, additional: usize) {
    self.container.reserve(additional);
  }
}

impl<E, Container> Errors<E, Container> {
  #[inline]
  const fn new_in(container: Container) -> Self {
    Self {
      container,
      _phantom: core::marker::PhantomData,
    }
  }
}

// Default trait implementations
impl<E, Container> Default for Errors<E, Container>
where
  Container: Default,
{
  #[inline]
  fn default() -> Self {
    Self::new_in(Container::default())
  }
}

// AsRef and AsMut implementations
impl<E, C> AsRef<[E]> for Errors<E, C>
where
  C: AsRef<[E]>,
{
  #[inline]
  fn as_ref(&self) -> &[E] {
    self.container.as_ref()
  }
}

impl<E, C> AsMut<[E]> for Errors<E, C>
where
  C: AsMut<[E]>,
{
  #[inline]
  fn as_mut(&mut self) -> &mut [E] {
    self.container.as_mut()
  }
}

// Display implementation for better error reporting
impl<E, C> Display for Errors<E, C>
where
  E: Display,
  C: AsRef<[E]>,
{
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let errors = self.container.as_ref();

    if errors.is_empty() {
      return Ok(());
    }

    if errors.len() == 1 {
      write!(f, "{}", errors[0])
    } else {
      writeln!(f, "{} errors:", errors.len())?;
      for (i, error) in errors.iter().enumerate() {
        write!(f, "  {}. {}", i + 1, error)?;
        if i < errors.len() - 1 {
          writeln!(f)?;
        }
      }
      Ok(())
    }
  }
}

impl<'a, E, Container> IntoIterator for &'a Errors<E, Container>
where
  &'a Container: IntoIterator<Item = E>,
{
  type Item = E;
  type IntoIter = <&'a Container as IntoIterator>::IntoIter;

  #[inline]
  fn into_iter(self) -> Self::IntoIter {
    self.container.into_iter()
  }
}

impl<E, Container> IntoIterator for Errors<E, Container>
where
  Container: IntoIterator<Item = E>,
{
  type Item = E;
  type IntoIter = Container::IntoIter;

  #[inline]
  fn into_iter(self) -> Self::IntoIter {
    self.container.into_iter()
  }
}

impl<E, Container> FromIterator<E> for Errors<E, Container>
where
  Container: FromIterator<E>,
{
  #[inline]
  fn from_iter<I: IntoIterator<Item = E>>(iter: I) -> Self {
    Self {
      container: Container::from_iter(iter),
      _phantom: core::marker::PhantomData,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_new() {
    let _: Errors<&str> = Errors::new();
  }

  #[test]
  fn test_push_and_len() {
    let mut errors = Errors::new();
    errors.push("Error 1");
    assert_eq!(errors.len(), 1);
    errors.push("Error 2");
    assert_eq!(errors.len(), 2);
  }

  #[test]
  fn test_clear() {
    let mut errors = Errors::new();
    errors.push("Error");
    errors.clear();
    assert!(errors.is_empty());
  }

  #[test]
  fn test_iteration() {
    let mut errors = Errors::new();
    errors.push(1);
    errors.push(2);

    let sum: i32 = errors.iter().sum();
    assert_eq!(sum, 3);
  }

  #[cfg(any(feature = "alloc", feature = "std"))]
  #[test]
  fn test_with_capacity() {
    let errors: Errors<&str> = Errors::with_capacity(10);
    assert_eq!(errors.capacity(), 10);
    assert!(errors.is_empty());
  }

  #[cfg(any(feature = "alloc", feature = "std"))]
  #[test]
  fn test_pop() {
    let mut errors = Errors::new();
    errors.push(1);
    errors.push(2);

    assert_eq!(errors.pop(), Some(2));
    assert_eq!(errors.pop(), Some(1));
    assert_eq!(errors.pop(), None);
  }
}
