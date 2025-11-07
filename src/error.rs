pub use errors::{DefaultContainer, Errors};

use generic_array::ArrayLength;
pub use hex_escape::*;
pub use incomplete_syntax::*;
pub use incomplete_token::*;
pub use invalid::*;
pub use invalid_hex_digits::*;
pub use malformed::*;
pub use unclosed::*;
pub use unexpected_end::*;
pub use unexpected_keyword::*;
pub use unexpected_lexeme::*;
pub use unexpected_prefix::*;
pub use unexpected_suffix::*;
pub use unexpected_token::*;
pub use unicode_escape::*;
pub use unknown_lexeme::*;
pub use unterminated::*;

use crate::utils::{ConstGenericVec, ConstGenericVecIter, GenericVec, GenericVecIter};

mod errors;

mod hex_escape;
mod incomplete_syntax;
mod incomplete_token;
mod invalid;
mod malformed;
mod unclosed;
mod unexpected_end;
mod unexpected_keyword;
mod unexpected_lexeme;
mod unexpected_prefix;
mod unexpected_suffix;
mod unexpected_token;
mod unknown_lexeme;
mod unterminated;

mod invalid_hex_digits;
mod unicode_escape;

/// A container of error types
pub trait ErrorContainer<E> {
  /// The iterator type for the container.
  type IntoIter: Iterator<Item = E>;
  /// The iterator type for references to the container.
  type Iter<'a>: Iterator<Item = &'a E>
  where
    Self: 'a,
    E: 'a;

  /// Create a new, empty container.
  fn new() -> Self;

  /// Create a new container with a specified capacity.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn with_capacity(_: usize) -> Self
  where
    Self: Sized,
  {
    Self::new()
  }

  /// Push an error into the collection.
  fn push(&mut self, error: E);

  /// Attempts to push an error, returning it back if the container is full.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn try_push(&mut self, error: E) -> Result<(), E>
  where
    Self: Sized,
  {
    self.push(error);
    Ok(())
  }

  /// Pop an error from the first of the collection.
  fn pop(&mut self) -> Option<E>;

  /// Returns `true` if the collection is empty.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns the number of errors in the collection.
  fn len(&self) -> usize;

  /// Returns an iterator over the errors in the collection.
  fn iter(&self) -> Self::Iter<'_>;

  /// Consumes the container and returns an iterator over the errors.
  fn into_iter(self) -> Self::IntoIter;

  /// Returns the remaining capacity if the container has a fixed upper bound.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining_capacity(&self) -> Option<usize> {
    None
  }
}

impl<E> ErrorContainer<E> for Option<E> {
  type IntoIter = core::option::IntoIter<E>;
  type Iter<'a>
    = core::option::Iter<'a, E>
  where
    E: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn new() -> Self {
    None
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push(&mut self, error: E) {
    self.get_or_insert(error);
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn try_push(&mut self, error: E) -> Result<(), E> {
    if self.is_some() {
      Err(error)
    } else {
      self.push(error);
      Ok(())
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop(&mut self) -> Option<E> {
    self.take()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    if self.is_some() { 1 } else { 0 }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn iter(&self) -> Self::Iter<'_> {
    Self::iter(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    <Self as IntoIterator>::into_iter(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining_capacity(&self) -> Option<usize> {
    Some(if self.is_some() { 0 } else { 1 })
  }
}

impl<E, N: ArrayLength> ErrorContainer<E> for GenericVec<E, N> {
  type IntoIter = GenericVecIter<E, N>;

  type Iter<'a>
    = core::slice::Iter<'a, E>
  where
    Self: 'a,
    E: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn new() -> Self {
    GenericVec::new()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push(&mut self, error: E) {
    self.push(error);
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn try_push(&mut self, error: E) -> Result<(), E> {
    GenericVec::try_push(self, error)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop(&mut self) -> Option<E> {
    self.pop_front()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    self.len()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn iter(&self) -> Self::Iter<'_> {
    self.as_slice().iter()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    IntoIterator::into_iter(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining_capacity(&self) -> Option<usize> {
    Some(self.remaining_capacity())
  }
}

impl<E, const N: usize> ErrorContainer<E> for ConstGenericVec<E, N> {
  type IntoIter = ConstGenericVecIter<E, N>;

  type Iter<'a>
    = core::slice::Iter<'a, E>
  where
    Self: 'a,
    E: 'a;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn new() -> Self {
    ConstGenericVec::new()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push(&mut self, error: E) {
    self.push(error);
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn try_push(&mut self, error: E) -> Result<(), E> {
    ConstGenericVec::try_push(self, error)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn pop(&mut self) -> Option<E> {
    self.pop_front()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn len(&self) -> usize {
    self.len()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn iter(&self) -> Self::Iter<'_> {
    self.as_slice().iter()
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    IntoIterator::into_iter(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn remaining_capacity(&self) -> Option<usize> {
    Some(self.remaining_capacity())
  }
}

#[cfg(any(feature = "std", feature = "alloc"))]
const _: () = {
  use std::{
    collections::{VecDeque, vec_deque},
    vec::{self, Vec},
  };

  impl<E> ErrorContainer<E> for Vec<E> {
    type IntoIter = vec::IntoIter<E>;
    type Iter<'a>
      = core::slice::Iter<'a, E>
    where
      E: 'a;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn new() -> Self {
      Self::new()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn with_capacity(capacity: usize) -> Self {
      Self::with_capacity(capacity)
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn push(&mut self, error: E) {
      self.push(error);
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn pop(&mut self) -> Option<E> {
      if self.is_empty() {
        None
      } else {
        Some(self.remove(0))
      }
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn len(&self) -> usize {
      self.len()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn iter(&self) -> Self::Iter<'_> {
      self.as_slice().iter()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_iter(self) -> Self::IntoIter {
      <Self as IntoIterator>::into_iter(self)
    }
  }

  impl<E> ErrorContainer<E> for VecDeque<E> {
    type IntoIter = vec_deque::IntoIter<E>;
    type Iter<'a>
      = vec_deque::Iter<'a, E>
    where
      E: 'a,
      Self: 'a;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn new() -> Self {
      Self::new()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn with_capacity(capacity: usize) -> Self {
      Self::with_capacity(capacity)
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn push(&mut self, error: E) {
      self.push_back(error);
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn pop(&mut self) -> Option<E> {
      self.pop_front()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn len(&self) -> usize {
      self.len()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn iter(&self) -> Self::Iter<'_> {
      self.iter()
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_iter(self) -> Self::IntoIter {
      <Self as IntoIterator>::into_iter(self)
    }
  }
};
