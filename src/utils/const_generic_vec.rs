//! Const-generic based bounded vector implementation.

use core::{
  mem::MaybeUninit,
  slice::{from_raw_parts, from_raw_parts_mut},
};

/// A stack-allocated, fixed-capacity vector that silently drops elements when full.
///
/// `ConstGenericVec` is a `no_std` compatible, zero-allocation container that can hold
/// at most `N` elements. It's designed specifically for error collection in no-alloc
/// environments where you want to collect the first N errors before giving up.
///
/// # Key Characteristics
///
/// - **Fixed capacity**: Can hold at most `N` elements (specified via const generic)
/// - **Zero allocation**: All storage is on the stack via `[MaybeUninit<T>; N]`
/// - **Silent overflow**: When full, `push()` silently drops new elements (by design)
/// - **Proper drop semantics**: Elements are properly dropped when the vector is dropped
///
/// # Design Rationale
///
/// Traditional `Vec` requires allocation, which isn't available in `no_std` environments.
/// `ArrayVec`-style types panic on overflow, but parsers often want to collect multiple
/// errors without panicking. This type provides a middle ground: collect the first N
/// errors, then silently ignore the rest.
///
/// # Comparison with Alternatives
///
/// | Type | Allocation | Overflow Behavior | Best For |
/// |------|------------|-------------------|----------|
/// | `Vec` | Heap | Grows dynamically | Standard environments |
/// | `ArrayVec` | Stack | Panics or returns error | Critical correctness |
/// | `ConstGenericVec` | Stack | Silently drops | Error collection |
///
/// # Examples
///
/// ## Basic Usage
///
/// ```rust
/// use logosky::utils::ConstGenericVec;
///
/// let mut errors: ConstGenericVec<&str, 8> = ConstGenericVec::new();
///
/// errors.push("error 1");
/// errors.push("error 2");
/// assert_eq!(errors.len(), 2);
/// assert_eq!(errors[0], "error 1");
/// ```
///
/// ## Error Collection Pattern
///
/// ```rust
/// use logosky::utils::ConstGenericVec;
///
/// fn parse(input: &str) -> Result<(), ConstGenericVec<String, 10>> {
///     let mut errors = ConstGenericVec::new();
///
///     for (i, line) in input.lines().enumerate() {
///         if line.trim().is_empty() {
///             errors.push(format!("Line {}: empty line", i));
///         }
///     }
///
///     if errors.is_empty() {
///         Ok(())
///     } else {
///         Err(errors)
///     }
/// }
/// ```
///
/// ## Overflow Behavior
///
/// ```rust
/// use logosky::utils::ConstGenericVec;
///
/// let mut vec: ConstGenericVec<i32, 2> = ConstGenericVec::new();
/// vec.push(1);
/// vec.push(2);
/// vec.push(3); // Silently dropped
/// vec.push(4); // Silently dropped
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec.as_slice(), &[1, 2]);
/// ```
#[derive(Debug)]
pub struct ConstGenericVec<T, const N: usize> {
  values: [MaybeUninit<T>; N],
  len: usize,
}

impl<T, const N: usize> Clone for ConstGenericVec<T, N>
where
  T: Clone,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    let mut new = Self::new();
    for value in self.iter() {
      // SAFETY: We're cloning from a vec with len <= N, so new vec won't exceed capacity.
      unsafe {
        new.push_unchecked(value.clone());
      }
    }
    new
  }
}

impl<T, const N: usize> FromIterator<T> for ConstGenericVec<T, N> {
  /// Creates a `ConstGenericVec` from an iterator, collecting at most `N` elements.
  ///
  /// Elements beyond the capacity are silently dropped.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let vec: ConstGenericVec<i32, 4> = (0..10).collect();
  /// assert_eq!(vec.len(), 4);
  /// assert_eq!(vec.as_slice(), &[0, 1, 2, 3]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut vec = Self::new();
    for item in iter {
      vec.push(item);
    }
    vec
  }
}

impl<T, const N: usize> AsRef<[T]> for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[T] {
    self
  }
}

impl<T, const N: usize> AsMut<[T]> for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_mut(&mut self) -> &mut [T] {
    self
  }
}

impl<T, const N: usize> core::ops::Deref for ConstGenericVec<T, N> {
  type Target = [T];

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref(&self) -> &Self::Target {
    self.as_slice()
  }
}

impl<T, const N: usize> core::ops::DerefMut for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.as_mut_slice()
  }
}

impl<T, const N: usize> Default for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self::new()
  }
}

impl<T, const N: usize> ConstGenericVec<T, N> {
  /// Create a new empty `ConstGenericVec`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let vec: ConstGenericVec<i32, 10> = ConstGenericVec::new();
  /// assert_eq!(vec.len(), 0);
  /// assert_eq!(vec.capacity(), 10);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new() -> Self {
    Self {
      values: [const { MaybeUninit::<T>::uninit() }; N],
      len: 0,
    }
  }

  /// Returns the maximum number of elements this vector can hold.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let vec: ConstGenericVec<i32, 16> = ConstGenericVec::new();
  /// assert_eq!(vec.capacity(), 16);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn capacity(&self) -> usize {
    N
  }

  /// Returns the number of elements currently in the vector.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// assert_eq!(vec.len(), 0);
  /// vec.push(1);
  /// assert_eq!(vec.len(), 1);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the vector contains no elements.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// assert!(vec.is_empty());
  /// vec.push(1);
  /// assert!(!vec.is_empty());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns `true` if the vector is at full capacity.
  ///
  /// When the vector is full, subsequent `push()` operations will silently drop elements.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 2> = ConstGenericVec::new();
  /// assert!(!vec.is_full());
  /// vec.push(1);
  /// vec.push(2);
  /// assert!(vec.is_full());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.len >= N
  }

  /// Returns the number of additional elements the vector can hold.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 5> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// assert_eq!(vec.remaining_capacity(), 3);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn remaining_capacity(&self) -> usize {
    N - self.len
  }

  /// Push a value to the end of the vector.
  ///
  /// If the vector is at capacity, the value is returned back to the caller.
  /// This is intentional behavior for error collection in no-alloc parsers.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 2> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3); // Dropped silently
  ///
  /// assert_eq!(vec.len(), 2);
  /// assert_eq!(vec.as_slice(), &[1, 2]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn push(&mut self, value: T) -> Option<T> {
    if self.len < N {
      self.values[self.len].write(value);
      self.len += 1;
      None
    } else {
      Some(value)
    }
  }

  /// Attempts to push a value, returning `Err(value)` if the vector is full.
  ///
  /// Unlike `push()`, this method allows you to detect and handle overflow.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 2> = ConstGenericVec::new();
  /// assert!(vec.try_push(1).is_ok());
  /// assert!(vec.try_push(2).is_ok());
  /// assert_eq!(vec.try_push(3), Err(3)); // Full!
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn try_push(&mut self, value: T) -> Result<(), T> {
    if self.len < N {
      self.values[self.len].write(value);
      self.len += 1;
      Ok(())
    } else {
      Err(value)
    }
  }

  /// Push a value to the end of the vector without checking capacity.
  ///
  /// # Safety
  ///
  /// The caller must ensure that `self.len() < self.capacity()`.
  /// Violating this results in undefined behavior.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// unsafe {
  ///     vec.push_unchecked(1);
  ///     vec.push_unchecked(2);
  /// }
  /// assert_eq!(vec.len(), 2);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const unsafe fn push_unchecked(&mut self, value: T) {
    self.values[self.len].write(value);
    self.len += 1;
  }

  /// Removes and returns the last element, or `None` if empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// assert_eq!(vec.pop(), Some(2));
  /// assert_eq!(vec.pop(), Some(1));
  /// assert_eq!(vec.pop(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn pop(&mut self) -> Option<T> {
    if self.len > 0 {
      self.len -= 1;
      // SAFETY: len was > 0, so there's a valid element at len - 1
      Some(unsafe { self.values[self.len].assume_init_read() })
    } else {
      None
    }
  }

  /// Clears the vector, dropping all elements.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.clear();
  ///
  /// assert_eq!(vec.len(), 0);
  /// assert!(vec.is_empty());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn clear(&mut self) {
    // Drop all initialized elements
    for i in 0..self.len {
      unsafe {
        self.values[i].assume_init_drop();
      }
    }
    self.len = 0;
  }

  /// Retains only elements that satisfy the predicate.
  ///
  /// Elements are visited in order, and those for which the predicate returns
  /// `false` are removed.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 8> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  /// vec.push(4);
  ///
  /// vec.retain(|&x| x % 2 == 0);
  /// assert_eq!(vec.as_slice(), &[2, 4]);
  /// ```
  pub fn retain<F>(&mut self, mut f: F)
  where
    F: FnMut(&T) -> bool,
  {
    let mut write_idx = 0;
    for read_idx in 0..self.len {
      // SAFETY: read_idx < self.len, so element is initialized
      let should_keep = unsafe {
        let elem_ref = &*self.values[read_idx].as_ptr();
        f(elem_ref)
      };

      if should_keep {
        if write_idx != read_idx {
          // SAFETY: Both indices are < len and point to initialized elements
          unsafe {
            let value = self.values[read_idx].assume_init_read();
            self.values[write_idx].write(value);
          }
        }
        write_idx += 1;
      } else {
        // SAFETY: read_idx < self.len, so element is initialized
        unsafe {
          self.values[read_idx].assume_init_drop();
        }
      }
    }
    self.len = write_idx;
  }

  /// Truncates the vector to `len` elements.
  ///
  /// If `len` is greater than the current length, this has no effect.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 8> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  /// vec.truncate(1);
  ///
  /// assert_eq!(vec.as_slice(), &[1]);
  /// ```
  pub fn truncate(&mut self, len: usize) {
    if len < self.len {
      // Drop elements from len..self.len
      for i in len..self.len {
        unsafe {
          self.values[i].assume_init_drop();
        }
      }
      self.len = len;
    }
  }

  /// Returns an iterator over the values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  ///
  /// let sum: i32 = vec.iter().sum();
  /// assert_eq!(sum, 6);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter(&self) -> core::slice::Iter<'_, T> {
    self.as_slice().iter()
  }

  /// Returns a mutable iterator over the values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// for x in vec.iter_mut() {
  ///     *x *= 2;
  /// }
  /// assert_eq!(vec.as_slice(), &[2, 4]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
    self.as_mut_slice().iter_mut()
  }

  /// Returns a slice of the values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// assert_eq!(vec.as_slice(), &[1, 2]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_slice(&self) -> &[T] {
    // SAFETY: We ensure that `self.len` is always <= N, and that all
    // elements in the range [0..len) are properly initialized.
    unsafe { from_raw_parts(self.values.as_ptr() as *const T, self.len) }
  }

  /// Returns a mutable slice of the values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// vec.as_mut_slice()[0] = 10;
  /// assert_eq!(vec.as_slice(), &[10, 2]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_slice(&mut self) -> &mut [T] {
    // SAFETY: We ensure that `self.len` is always <= N, and that all
    // elements in the range [0..len) are properly initialized.
    unsafe { from_raw_parts_mut(self.values.as_mut_ptr() as *mut T, self.len) }
  }

  /// Returns a pointer to the first element.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  ///
  /// let ptr = vec.as_ptr();
  /// unsafe {
  ///     assert_eq!(*ptr, 1);
  /// }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_ptr(&self) -> *const T {
    self.values.as_ptr() as *const T
  }

  /// Returns a mutable pointer to the first element.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::utils::ConstGenericVec;
  ///
  /// let mut vec: ConstGenericVec<i32, 4> = ConstGenericVec::new();
  /// vec.push(1);
  ///
  /// let ptr = vec.as_mut_ptr();
  /// unsafe {
  ///     *ptr = 10;
  /// }
  /// assert_eq!(vec[0], 10);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_ptr(&mut self) -> *mut T {
    self.values.as_mut_ptr() as *mut T
  }
}

impl<T, const N: usize> Drop for ConstGenericVec<T, N> {
  fn drop(&mut self) {
    self.clear();
  }
}

impl<T, I, const N: usize> core::ops::Index<I> for ConstGenericVec<T, N>
where
  I: core::slice::SliceIndex<[T]>,
{
  type Output = I::Output;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index(&self, index: I) -> &Self::Output {
    &self.as_slice()[index]
  }
}

impl<T, I, const N: usize> core::ops::IndexMut<I> for ConstGenericVec<T, N>
where
  I: core::slice::SliceIndex<[T]>,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index_mut(&mut self, index: I) -> &mut Self::Output {
    &mut self.as_mut_slice()[index]
  }
}

impl<T: PartialEq, const N: usize> PartialEq for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    self.as_slice() == other.as_slice()
  }
}

impl<T: Eq, const N: usize> Eq for ConstGenericVec<T, N> {}

impl<T: PartialOrd, const N: usize> PartialOrd for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    self.as_slice().partial_cmp(other.as_slice())
  }
}

impl<T: Ord, const N: usize> Ord for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.as_slice().cmp(other.as_slice())
  }
}

impl<T: core::hash::Hash, const N: usize> core::hash::Hash for ConstGenericVec<T, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.as_slice().hash(state);
  }
}
