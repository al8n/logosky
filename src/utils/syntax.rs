use generic_array::typenum::Unsigned;

pub use generic_array::{ArrayLength, GenericArray, GenericArrayIter, typenum};

use core::{
  fmt::{Debug, Display},
  hash::Hash,
  mem::MaybeUninit,
};

/// A trait representing a syntax with components.
pub trait Syntax {
  /// The component type of this syntax.
  /// Usually the type is an enum representing different variants.
  /// This type is used for error reporting.
  type Component: Display + Debug + Clone + PartialEq + Eq + Hash;

  /// The number of components in this syntax, represented as a type-level unsigned integer.
  ///
  /// Uses `typenum` to represent the count at the type level, avoiding the need for
  /// unstable `generic_const_exprs` feature.
  ///
  /// # Examples
  ///
  /// ```rust,ignore
  /// use logosky::Syntax;
  /// use typenum::U2; // For an element with 2 components
  ///
  /// impl Syntax for MyElement {
  ///     type Components = U2;
  ///     // ...
  /// }
  /// ```
  type COMPONENTS: ArrayLength + Debug + Eq + Hash;

  /// Returns an array holds all possible components for this syntax.
  fn possible_components() -> GenericArray<Self::Component, Self::COMPONENTS>;
}

/// Represents an incomplete syntax with missing components.
///
/// This type stores the missing components as a set (no duplicates allowed).
/// It always contains at least one component.
#[derive(Debug)]
pub struct IncompleteSyntax<S: Syntax> {
  len: usize,
  buf: GenericArray<MaybeUninit<S::Component>, S::COMPONENTS>,
}

impl<S> Clone for IncompleteSyntax<S>
where
  S: Syntax,
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

impl<S> PartialEq for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    if self.len != other.len {
      return false;
    }
    self.as_slice().eq(other.as_slice())
  }
}

impl<S> Eq for IncompleteSyntax<S> where S: Syntax {}

impl<S> Hash for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.as_slice().hash(state);
  }
}

impl<S> AsRef<[S::Component]> for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[S::Component] {
    self.as_slice()
  }
}

impl<S> AsMut<[S::Component]> for IncompleteSyntax<S>
where
  S: Syntax,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_mut(&mut self) -> &mut [S::Component] {
    self.as_mut_slice()
  }
}

impl<S> IncompleteSyntax<S>
where
  S: Syntax,
{
  /// Creates a new incomplete syntax with the specified component.
  ///
  /// The buffer always contains at least one component.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(component: S::Component) -> Self {
    let mut buf = GenericArray::uninit();

    if S::COMPONENTS::USIZE == 0 {
      panic!("IncompleteSyntax requires the COMPONENTS associated type of Syntax to be non-zero");
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
  #[allow(clippy::should_implement_trait)]
  pub fn from_iter(iter: impl IntoIterator<Item = S::Component>) -> Option<Self> {
    let mut instance = Self {
      len: 0,
      buf: GenericArray::uninit(),
    };
    for component in iter {
      instance.try_push(component)?;
    }
    instance.len().ne(&0).then_some(instance)
  }

  /// Returns the number of components in the incomplete syntax.
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
  pub fn push(&mut self, component: S::Component) {
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
  pub fn try_push(&mut self, component: S::Component) -> Option<S::Component> {
    // Check for duplicates - if already present, treat as success
    if self.as_slice().contains(&component) {
      return None;
    }

    if self.len < S::COMPONENTS::USIZE {
      self.buf[self.len].write(component);
      self.len += 1;
      None
    } else {
      Some(component)
    }
  }

  /// Returns a slice of the components in the buffer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_slice(&self) -> &[S::Component] {
    // SAFETY: We ensure that only initialized components are accessed.
    unsafe {
      core::slice::from_raw_parts(
        self.buf.as_slice().as_ptr() as *const S::Component,
        self.len,
      )
    }
  }

  /// Returns a mutable slice of the components in the buffer.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_slice(&mut self) -> &mut [S::Component] {
    // SAFETY: We ensure that only initialized components are accessed.
    unsafe {
      core::slice::from_raw_parts_mut(
        self.buf.as_mut_slice().as_mut_ptr() as *mut S::Component,
        self.len,
      )
    }
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
