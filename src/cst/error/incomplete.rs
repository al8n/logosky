use core::mem::MaybeUninit;

use crate::cst::CstNode;
use generic_array::{GenericArray, typenum::Unsigned};

/// Represents an incomplete syntax element with missing components.
///
/// This type stores the missing components as a set (no duplicates allowed).
/// It always contains at least one component.
#[derive(Debug)]
pub struct IncompleteSyntax<C: CstNode> {
  len: usize,
  buf: GenericArray<MaybeUninit<C::Component>, C::COMPONENTS>,
}

impl<C> Clone for IncompleteSyntax<C>
where
  C: CstNode,
  C::Component: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    let mut new_buf = GenericArray::uninit();
    for i in 0..self.len {
      // SAFETY: We know indices 0..len are initialized
      unsafe {
        let value = (*self.buf[i].as_ptr()).clone();
        new_buf[i].write(value);
      }
    }
    Self {
      len: self.len,
      buf: new_buf,
    }
  }
}

impl<C> PartialEq for IncompleteSyntax<C>
where
  C: CstNode,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    if self.len != other.len {
      return false;
    }
    self.as_slice().eq(other.as_slice())
  }
}

impl<C> Eq for IncompleteSyntax<C> where C: CstNode {}

impl<C> core::hash::Hash for IncompleteSyntax<C>
where
  C: CstNode,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.as_slice().hash(state);
  }
}

impl<C: CstNode> AsRef<[C::Component]> for IncompleteSyntax<C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[C::Component] {
    self.as_slice()
  }
}

impl<C: CstNode> AsMut<[C::Component]> for IncompleteSyntax<C> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_mut(&mut self) -> &mut [C::Component] {
    self.as_mut_slice()
  }
}

impl<C: CstNode> IncompleteSyntax<C> {
  /// Creates a new incomplete syntax element with the specified component.
  ///
  /// The buffer always contains at least one component.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(component: C::Component) -> Self {
    let mut buf = GenericArray::uninit();

    if C::COMPONENTS::USIZE == 0 {
      panic!("IncompleteSyntax requires the COMPONENTS associated type of CstNode to be non-zero");
    }

    // SAFETY: We are initializing the first element of the buffer.
    unsafe {
      core::ptr::write(buf.as_mut_slice().as_mut_ptr(), MaybeUninit::new(component));
    }
    Self { len: 1, buf }
  }

  /// Tries to create an incomplete syntax from an iterator of components.
  ///
  /// Returns `None` if the iterator yields no components or more components than the buffer can hold.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn from_iter(iter: impl IntoIterator<Item = C::Component>) -> Option<Self> {
    let mut instance = Self {
      len: 0,
      buf: GenericArray::uninit(),
    };
    for component in iter {
      instance.try_push(component)?;
    }
    instance.len().ne(&0).then_some(instance)
  }

  /// Returns the number of components in the incomplete syntax element.
  ///
  /// The length is always at least 1.
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[allow(clippy::len_without_is_empty)]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Pushes a new component into the buffer.
  ///
  /// If the component already exists in the buffer, this is a no-op (silently succeeds).
  ///
  /// # Panics
  /// - Panics if the buffer is already full and the component is not already present.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn push(&mut self, component: C::Component) {
    if self.try_push(component).is_some() {
      panic!("IncompleteSyntaxBuffer overflow: cannot push more components")
    }
  }

  /// Tries to push a new component into the buffer.
  ///
  /// If the component already exists in the buffer, returns `None` (silently succeeds).
  ///
  /// Returns `Some(component)` only if the buffer is full and the component is not already present.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn try_push(&mut self, component: C::Component) -> Option<C::Component> {
    // Check for duplicates - if already present, treat as success
    if self.as_slice().contains(&component) {
      return None;
    }

    if self.len < C::COMPONENTS::USIZE {
      self.buf[self.len].write(component);
      self.len += 1;
      None
    } else {
      Some(component)
    }
  }

  /// Returns a slice of the components in the buffer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_slice(&self) -> &[C::Component] {
    // SAFETY: We ensure that only initialized components are accessed.
    unsafe {
      core::slice::from_raw_parts(
        self.buf.as_slice().as_ptr() as *const C::Component,
        self.len,
      )
    }
  }

  /// Returns a mutable slice of the components in the buffer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_slice(&mut self) -> &mut [C::Component] {
    // SAFETY: We ensure that only initialized components are accessed.
    unsafe {
      core::slice::from_raw_parts_mut(
        self.buf.as_mut_slice().as_mut_ptr() as *mut C::Component,
        self.len,
      )
    }
  }
}

impl<C: CstNode> core::fmt::Display for IncompleteSyntax<C> {
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let components = self.as_slice();

    if components.len() == 1 {
      write!(
        f,
        "incomplete syntax element: component {} is missing",
        components[0]
      )
    } else {
      write!(f, "incomplete syntax element: components ")?;
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

impl<C: CstNode> core::error::Error for IncompleteSyntax<C> {}
