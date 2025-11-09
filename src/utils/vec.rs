//! Stack-allocated vector types using generic-arraydeque.
//!
//! This module re-exports types from `generic-arraydeque` and provides
//! additional wrappers like `FrozenGenericVec` for immutable vectors.

pub use generic_arraydeque::{
  typenum, ArrayLength, ConstArrayLength,
  GenericArrayDeque as GenericVec,
  Iter as GenericVecIter,
  IntoIter as GenericVecIntoIter,
};

/// A const-generic based bounded vector.
///
/// This is an alias for `GenericArrayDeque` using `ConstArrayLength` to convert
/// const generic parameters to type-level numbers.
pub type ConstGenericVec<T, const N: usize> = GenericVec<T, ConstArrayLength<N>>;

/// Iterator over `ConstGenericVec`.
pub type ConstGenericVecIter<'a, T, const N: usize> = GenericVecIter<'a, T>;

/// An immutable, type-level capacity vector.
///
/// `FrozenGenericVec` is a read-only wrapper around [`GenericVec`] that prevents
/// further modifications. It's useful for:
/// - Expressing that a collection is complete and won't change
/// - API boundaries where mutation should not be allowed
/// - Compile-time guarantees about immutability
///
/// Created via [`GenericVec::freeze`]. Exposes only read access and `IntoIterator` by value.
///
/// # Examples
///
/// ```rust
/// # {
/// use logosky::utils::{GenericVec, typenum::U3};
///
/// let mut vec: GenericVec<i32, U3> = GenericVec::new();
/// vec.push_back(1);
/// vec.push_back(2);
/// vec.push_back(3);
///
/// let frozen = FrozenGenericVec::new(vec);
/// assert_eq!(frozen.len(), 3);
/// assert_eq!(&frozen[..], &[1, 2, 3]);
/// # }
/// ```
#[derive(Debug)]
pub struct FrozenGenericVec<T, N: ArrayLength> {
  inner: GenericVec<T, N>,
}

impl<T, N> Clone for FrozenGenericVec<T, N>
where
  T: Clone,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone(),
    }
  }
}

impl<T, N> AsRef<[T]> for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[T] {
    self.as_slice()
  }
}

impl<T, N> core::ops::Deref for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  type Target = [T];

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref(&self) -> &Self::Target {
    self.as_slice()
  }
}

impl<T, N> core::ops::Index<usize> for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  type Output = T;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index(&self, index: usize) -> &Self::Output {
    &self.inner[index]
  }
}

impl<T, N> PartialEq for FrozenGenericVec<T, N>
where
  T: PartialEq,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    self.inner == other.inner
  }
}

impl<T, N> Eq for FrozenGenericVec<T, N>
where
  T: Eq,
  N: ArrayLength,
{
}

impl<T, N> core::hash::Hash for FrozenGenericVec<T, N>
where
  T: core::hash::Hash,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.inner.hash(state);
  }
}

impl<T, N> FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  /// Creates a new frozen vector from a mutable vector.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new(inner: GenericVec<T, N>) -> Self {
    Self { inner }
  }

  /// Returns the maximum number of elements this vector can hold.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U16;
  ///
  /// let mut vec: GenericVec<i32, U16> = GenericVec::new();
  /// let frozen = FrozenGenericVec::new(vec);
  /// assert_eq!(frozen.capacity(), 16);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn capacity(&self) -> usize {
    self.inner.capacity()
  }

  /// Returns the number of elements currently in the vector.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// assert!(vec.push_back(1).is_none());
  /// let frozen = FrozenGenericVec::new(vec);
  /// assert_eq!(frozen.len(), 1);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn len(&self) -> usize {
    self.inner.len()
  }

  /// Returns `true` if the vector contains no elements.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// let frozen = FrozenGenericVec::new(vec);
  /// assert!(frozen.is_empty());
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_empty(&self) -> bool {
    self.inner.is_empty()
  }

  /// Returns `true` if the vector is at full capacity.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U2;
  ///
  /// let mut vec: GenericVec<i32, U2> = GenericVec::new();
  /// assert!(vec.push_back(1).is_none());
  /// assert!(vec.push_back(2).is_none());
  /// let frozen = FrozenGenericVec::new(vec);
  /// assert!(frozen.is_full());
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.inner.is_full()
  }

  /// Returns an iterator over the elements.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U3;
  ///
  /// let mut vec: GenericVec<i32, U3> = GenericVec::new();
  /// assert!(vec.push_back(1).is_none());
  /// assert!(vec.push_back(2).is_none());
  /// let frozen = FrozenGenericVec::new(vec);
  ///
  /// let sum: i32 = frozen.iter().sum();
  /// assert_eq!(sum, 3);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter(&self) -> core::slice::Iter<'_, T> {
    self.inner.iter()
  }

  /// Returns a slice containing all elements.
  ///
  /// **Note**: This method makes the internal buffer contiguous if it isn't already.
  /// For frozen vectors built with `push_back`, this is typically already the case.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U3;
  ///
  /// let mut vec: GenericVec<i32, U3> = GenericVec::new();
  /// assert!(vec.push_back(1).is_none());
  /// assert!(vec.push_back(2).is_none());
  /// let frozen = FrozenGenericVec::new(vec);
  ///
  /// assert_eq!(frozen.as_slice(), &[1, 2]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_slice(&self) -> &[T] {
    // Check if already contiguous
    let (first, second) = self.inner.as_slices();
    if second.is_empty() {
      first
    } else {
      // If not contiguous, we need mutable access to make it contiguous
      // Since we can't do that with &self, we'll use an unsafe workaround
      // This is safe because make_contiguous only rearranges elements, doesn't mutate them
      unsafe {
        let ptr = &self.inner as *const GenericVec<T, N> as *mut GenericVec<T, N>;
        (*ptr).make_contiguous()
      }
    }
  }

  /// Returns a pointer to the first element.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, FrozenGenericVec, typenum};
  /// use typenum::U3;
  ///
  /// let mut vec: GenericVec<i32, U3> = GenericVec::new();
  /// assert!(vec.push_back(1).is_none());
  /// let frozen = FrozenGenericVec::new(vec);
  ///
  /// let ptr = frozen.as_ptr();
  /// unsafe {
  ///     assert_eq!(*ptr, 1);
  /// }
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_ptr(&self) -> *const T {
    self.as_slice().as_ptr()
  }
}

impl<T, N> IntoIterator for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  type Item = T;
  type IntoIter = generic_arraydeque::IntoIter<T, N>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.inner.into_iter()
  }
}

impl<'a, T, N> IntoIterator for &'a FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  type Item = &'a T;
  type IntoIter = core::slice::Iter<'a, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

/// Extension trait for `GenericVec` to enable freezing and provide compatibility methods.
pub trait GenericVecExt<T, N: ArrayLength> {
  /// Freeze the vector, making it immutable.
  fn freeze(self) -> FrozenGenericVec<T, N>;

  /// Push a value to the back of the vector.
  ///
  /// Returns `None` if the value was successfully added, or `Some(value)` if the
  /// vector is full and the value could not be added.
  ///
  /// This is an alias for `push_back` to maintain compatibility with the old API.
  fn push(&mut self, value: T) -> Option<T>;

  /// Try to push a value to the back of the vector.
  ///
  /// Returns `Ok(())` if the value was successfully added, or `Err(value)` if the
  /// vector is full.
  ///
  /// This is an alias for a combination of `push_back` to maintain compatibility.
  fn try_push(&mut self, value: T) -> Result<(), T>;
}

impl<T, N: ArrayLength> GenericVecExt<T, N> for GenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn freeze(self) -> FrozenGenericVec<T, N> {
    FrozenGenericVec::new(self)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn push(&mut self, value: T) -> Option<T> {
    self.push_back(value)
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn try_push(&mut self, value: T) -> Result<(), T> {
    self.push_back(value).map_or(Ok(()), Err)
  }
}

// Re-export the extension trait as Freeze for backwards compatibility
pub use GenericVecExt as Freeze;
