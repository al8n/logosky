//! Type-level capacity vector implementation using generic-array.
//!
//! This implementation uses `generic_array` and `typenum` to specify capacity
//! at the type level. This is useful for:
//! - Type-level capacity computation
//! - Integration with generic-array-based code
//! - Situations where capacity needs to be part of the type system
//!
//! # Key Characteristics
//!
//! - **Type-level capacity**: Capacity specified via `ArrayLength` (e.g., `U8`, `U16`)
//! - **Zero allocation**: All storage is on the stack
//! - **Overflow-aware**: `push`/`try_push` never panic; they return the unused value
//!   on overflow. If you ignore the return, extra elements are effectively dropped,
//!   which is useful for bounded error collection.
//! - **Proper drop semantics**: Elements in `[0..len)` are dropped exactly once.

use core::{
  mem::{ManuallyDrop, MaybeUninit},
  slice::{from_raw_parts, from_raw_parts_mut},
};

use generic_array::{ArrayLength, GenericArray};

/// A stack-allocated, fixed-capacity vector with type-level capacity specification.
///
/// `GenericVec` uses `ArrayLength` to encode the capacity as a type-level
/// number (via `typenum`). This enables compile-time capacity computation and better
/// integration with type-level programming patterns.
///
/// # Type-Level Numbers
///
/// Use `typenum` constants for capacity:
/// - `U1` through `U1024` for small sizes
/// - Arithmetic types like `Sum<U8, U4>` for computed sizes
///
/// ## Examples
///
/// ## Basic Usage
///
/// ```rust
/// # {
/// use logosky::utils::{GenericVec, typenum};
/// use typenum::U8;
///
/// let mut errors: GenericVec<&str, U8> = GenericVec::new();
///
/// errors.push("error 1");
/// errors.push("error 2");
/// assert_eq!(errors.len(), 2);
/// assert_eq!(errors[0], "error 1");
/// # }
/// ```
///
/// ## Error Collection Pattern
///
/// ```rust
/// # {
/// use logosky::utils::{GenericVec, typenum};
/// use typenum::U10;
///
/// fn parse(input: &str) -> Result<(), GenericVec<String, U10>> {
///     let mut errors = GenericVec::new();
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
/// # }
/// ```
///
/// ## Type-Level Capacity Arithmetic
///
/// ```rust
/// # {
/// use logosky::utils::{GenericVec, typenum};
/// use typenum::{U4, U8, Sum};
///
/// type MyCapacity = Sum<U4, U8>; // U4 + U8 = U12
/// let vec: GenericVec<i32, MyCapacity> = GenericVec::new();
/// assert_eq!(vec.capacity(), 12);
/// # }
/// ```
///
/// ## Overflow Behavior
///
/// ```rust
/// # {
/// use logosky::utils::{GenericVec, typenum};
/// use typenum::U2;
///
/// let mut vec: GenericVec<i32, U2> = GenericVec::new();
/// assert!(vec.push(1).is_none());
/// assert!(vec.push(2).is_none());
/// let overflow = vec.push(3);
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec.as_slice(), &[1, 2]);
/// assert_eq!(overflow, Some(3)); // caller can observe overflow
/// # }
/// ```
#[derive(Debug)]
pub struct GenericVec<T, N: ArrayLength> {
  values: GenericArray<MaybeUninit<T>, N>,
  len: usize,
}

impl<T, N> Clone for GenericVec<T, N>
where
  T: Clone,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    let mut new = Self::new();
    for value in self.iter() {
      // SAFETY: we never exceed capacity because self.len <= capacity.
      unsafe {
        new.push_unchecked(value.clone());
      }
    }
    new
  }
}

impl<T, N> FromIterator<T> for GenericVec<T, N>
where
  N: ArrayLength,
{
  /// Creates a `GenericVec` from an iterator, collecting at most N elements.
  ///
  /// Elements beyond the capacity are left in the iterator (if observed via `push`
  /// return values) or effectively dropped if ignored.
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let vec: GenericVec<i32, U4> = (0..10).collect();
  /// assert_eq!(vec.len(), 4);
  /// assert_eq!(vec.as_slice(), &[0, 1, 2, 3]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut vec = Self::new();
    for item in iter {
      let _ = vec.push(item);
    }
    vec
  }
}

impl<T, N> AsRef<[T]> for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_ref(&self) -> &[T] {
    self
  }
}

impl<T, N> AsMut<[T]> for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn as_mut(&mut self) -> &mut [T] {
    self
  }
}

impl<T, N> core::ops::Deref for GenericVec<T, N>
where
  N: ArrayLength,
{
  type Target = [T];

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref(&self) -> &Self::Target {
    self.as_slice()
  }
}

impl<T, N> core::ops::DerefMut for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.as_mut_slice()
  }
}

impl<T, N> Default for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self::new()
  }
}

impl<T, N> GenericVec<T, N>
where
  N: ArrayLength,
{
  /// Create a new empty `GenericVec`.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let vec: GenericVec<i32, U4> = GenericVec::new();
  /// assert_eq!(vec.len(), 0);
  /// assert_eq!(vec.capacity(), 4);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new() -> Self {
    Self {
      values: GenericArray::uninit(),
      len: 0,
    }
  }

  /// Returns the maximum number of elements this vector can hold.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U16;
  ///
  /// let vec: GenericVec<i32, U16> = GenericVec::new();
  /// assert_eq!(vec.capacity(), 16);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn capacity(&self) -> usize {
    N::USIZE
  }

  /// Returns the number of elements currently in the vector.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// assert_eq!(vec.len(), 0);
  /// vec.push(1);
  /// assert_eq!(vec.len(), 1);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the vector contains no elements.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// assert!(vec.is_empty());
  /// vec.push(1);
  /// assert!(!vec.is_empty());
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns `true` if the vector is at full capacity.
  ///
  /// When full, `push`/`try_push` will report overflow.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U2;
  ///
  /// let mut vec: GenericVec<i32, U2> = GenericVec::new();
  /// assert!(!vec.is_full());
  /// vec.push(1);
  /// vec.push(2);
  /// assert!(vec.is_full());
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.len >= N::USIZE
  }

  /// Returns the number of additional elements the vector can hold.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U5;
  ///
  /// let mut vec: GenericVec<i32, U5> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// assert_eq!(vec.remaining_capacity(), 3);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn remaining_capacity(&self) -> usize {
    N::USIZE - self.len
  }

  /// Push a value to the end of the vector.
  ///
  /// If the vector is at capacity, returns `Some(value)` and does not modify `self`.
  /// If you ignore the return value, overflow behaves like "silent drop".
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U2;
  ///
  /// let mut vec: GenericVec<i32, U2> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3); // Dropped silently
  ///
  /// assert_eq!(vec.len(), 2);
  /// assert_eq!(vec.as_slice(), &[1, 2]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn push(&mut self, value: T) -> Option<T> {
    if self.len < N::USIZE {
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
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U2;
  ///
  /// let mut vec: GenericVec<i32, U2> = GenericVec::new();
  /// assert!(vec.try_push(1).is_ok());
  /// assert!(vec.try_push(2).is_ok());
  /// assert_eq!(vec.try_push(3), Err(3)); // Full!
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn try_push(&mut self, value: T) -> Result<(), T> {
    if self.len < N::USIZE {
      self.values[self.len].write(value);
      self.len += 1;
      Ok(())
    } else {
      Err(value)
    }
  }

  /// Push a value without checking capacity.
  ///
  /// ## Safety
  ///
  /// The caller must ensure that `self.len() < self.capacity()`.
  /// Violating this results in undefined behavior.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// unsafe {
  ///     vec.push_unchecked(1);
  ///     vec.push_unchecked(2);
  /// }
  /// assert_eq!(vec.len(), 2);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub unsafe fn push_unchecked(&mut self, value: T) {
    self.values[self.len].write(value);
    self.len += 1;
  }

  /// Removes and returns the last element, or `None` if empty.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// assert_eq!(vec.pop(), Some(2));
  /// assert_eq!(vec.pop(), Some(1));
  /// assert_eq!(vec.pop(), None);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn pop(&mut self) -> Option<T> {
    if self.len > 0 {
      self.len -= 1;
      // SAFETY: element at `self.len` was initialized and is now removed.
      Some(unsafe { self.values[self.len].assume_init_read() })
    } else {
      None
    }
  }

  /// Removes and returns the first element, or `None` if empty.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// assert_eq!(vec.pop_front(), Some(1));
  /// assert_eq!(vec.pop_front(), Some(2));
  /// assert_eq!(vec.pop_front(), None);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn pop_front(&mut self) -> Option<T> {
    if self.len == 0 {
      return None;
    }

    // Take the first element.
    let first = unsafe { self.values[0].assume_init_read() };

    if self.len > 1 {
      unsafe {
        let base = self.values.as_mut_ptr();
        // Shift initialized range [1..len) down to [0..len-1).
        core::ptr::copy(base.add(1), base, self.len - 1);
        // The last slot now holds a duplicate; drop that extra copy.
        self.values[self.len - 1].assume_init_drop();
      }
    }

    self.len -= 1;
    Some(first)
  }

  /// Clears the vector, dropping all elements.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.clear();
  ///
  /// assert_eq!(vec.len(), 0);
  /// assert!(vec.is_empty());
  /// # }
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
  /// Elements are visited in order; those for which `f(&element)` returns `false` are removed.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U8;
  ///
  /// let mut vec: GenericVec<i32, U8> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  /// vec.push(4);
  ///
  /// vec.retain(|&x| x % 2 == 0);
  /// assert_eq!(vec.as_slice(), &[2, 4]);
  /// # }
  /// ```
  pub fn retain<F>(&mut self, mut f: F)
  where
    F: FnMut(&T) -> bool,
  {
    let mut write_idx = 0;
    for read_idx in 0..self.len {
      let keep = unsafe {
        // read_idx < self.len: element is initialized
        let elem_ref = &*self.values[read_idx].as_ptr();
        f(elem_ref)
      };

      if keep {
        if write_idx != read_idx {
          unsafe {
            let value = self.values[read_idx].assume_init_read();
            self.values[write_idx].write(value);
          }
        }
        write_idx += 1;
      } else {
        unsafe {
          self.values[read_idx].assume_init_drop();
        }
      }
    }
    self.len = write_idx;
  }

  /// Truncates the vector to `len` elements.
  ///
  /// If `len` is greater than current length, no-op.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U8;
  ///
  /// let mut vec: GenericVec<i32, U8> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  /// vec.truncate(1);
  ///
  /// assert_eq!(vec.as_slice(), &[1]);
  /// # }
  /// ```
  pub fn truncate(&mut self, len: usize) {
    if len < self.len {
      for i in len..self.len {
        unsafe {
          self.values[i].assume_init_drop();
        }
      }
      self.len = len;
    }
  }

  /// Returns an iterator over `&T`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  ///
  /// let sum: i32 = vec.iter().sum();
  /// assert_eq!(sum, 6);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter(&self) -> core::slice::Iter<'_, T> {
    self.as_slice().iter()
  }

  /// Returns an iterator over `&mut T`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// for x in vec.iter_mut() {
  ///     *x *= 2;
  /// }
  /// assert_eq!(vec.as_slice(), &[2, 4]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
    self.as_mut_slice().iter_mut()
  }

  /// Returns a slice of initialized values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// assert_eq!(vec.as_slice(), &[1, 2]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_slice(&self) -> &[T] {
    unsafe { from_raw_parts(self.values.as_ptr() as *const T, self.len) }
  }

  /// Returns a mutable slice of initialized values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  ///
  /// vec.as_mut_slice()[0] = 10;
  /// assert_eq!(vec.as_slice(), &[10, 2]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_mut_slice(&mut self) -> &mut [T] {
    unsafe { from_raw_parts_mut(self.values.as_mut_ptr() as *mut T, self.len) }
  }

  /// Returns a pointer to the first element.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  ///
  /// let ptr = vec.as_ptr();
  /// unsafe {
  ///     assert_eq!(*ptr, 1);
  /// }
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_ptr(&self) -> *const T {
    self.values.as_ptr() as *const T
  }

  /// Returns a mutable pointer to the first element.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  ///
  /// let ptr = vec.as_mut_ptr();
  /// unsafe {
  ///     *ptr = 10;
  /// }
  /// assert_eq!(vec[0], 10);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_mut_ptr(&mut self) -> *mut T {
    self.values.as_mut_ptr() as *mut T
  }
}

impl<T, N> Drop for GenericVec<T, N>
where
  N: ArrayLength,
{
  fn drop(&mut self) {
    self.clear();
  }
}

impl<T, I, N> core::ops::Index<I> for GenericVec<T, N>
where
  I: core::slice::SliceIndex<[T]>,
  N: ArrayLength,
{
  type Output = I::Output;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index(&self, index: I) -> &Self::Output {
    &self.as_slice()[index]
  }
}

impl<T, I, N> core::ops::IndexMut<I> for GenericVec<T, N>
where
  I: core::slice::SliceIndex<[T]>,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index_mut(&mut self, index: I) -> &mut Self::Output {
    &mut self.as_mut_slice()[index]
  }
}

impl<T: PartialEq, N> PartialEq for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    self.as_slice() == other.as_slice()
  }
}

impl<T: Eq, N> Eq for GenericVec<T, N> where N: ArrayLength {}

impl<T: PartialOrd, N> PartialOrd for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    self.as_slice().partial_cmp(other.as_slice())
  }
}

impl<T: Ord, N> Ord for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.as_slice().cmp(other.as_slice())
  }
}

impl<T: core::hash::Hash, N> core::hash::Hash for GenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.as_slice().hash(state);
  }
}

impl<'a, T, N> IntoIterator for &'a GenericVec<T, N>
where
  N: ArrayLength,
{
  type Item = &'a T;
  type IntoIter = core::slice::Iter<'a, T>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.as_slice().iter()
  }
}

/// An iterator that moves out elements from a `GenericVec`.
///
/// Owns the underlying storage via `ManuallyDrop<GenericVec<..>>` to avoid
/// running `GenericVec::drop` on moved-out elements. Any unyielded elements
/// are dropped when the iterator is dropped.
#[derive(Debug)]
pub struct GenericVecIter<T, N: ArrayLength> {
  this: ManuallyDrop<GenericVec<T, N>>,
  next: usize,
  end: usize,
}

impl<T, N> IntoIterator for GenericVec<T, N>
where
  N: ArrayLength,
{
  type Item = T;
  type IntoIter = GenericVecIter<T, N>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    let len = self.len();
    GenericVecIter {
      this: ManuallyDrop::new(self),
      next: 0,
      end: len,
    }
  }
}

impl<T, N: ArrayLength> Iterator for GenericVecIter<T, N> {
  type Item = T;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn next(&mut self) -> Option<Self::Item> {
    if self.next < self.end {
      let i = self.next;
      self.next += 1;
      // SAFETY:
      // - `[0..end)` was initialized in the original `GenericVec`.
      // - Each index in `[0..next)` is yielded at most once.
      Some(unsafe { self.this.values[i].assume_init_read() })
    } else {
      None
    }
  }

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let remaining = self.end - self.next;
    (remaining, Some(remaining))
  }
}

impl<T, N: ArrayLength> core::iter::ExactSizeIterator for GenericVecIter<T, N> {}

impl<T, N: ArrayLength> core::iter::FusedIterator for GenericVecIter<T, N> {}

impl<T, N: ArrayLength> Drop for GenericVecIter<T, N> {
  fn drop(&mut self) {
    // Drop only elements that have not yet been yielded.
    for i in self.next..self.end {
      unsafe {
        self.this.values[i].assume_init_drop();
      }
    }
    // `self.this` is `ManuallyDrop`, so `GenericVec::drop` is not called.
  }
}

/// A frozen (read-only) version of `GenericVec`.
///
/// Created via [`GenericVec::freeze`]. Exposes only read access and `IntoIterator` by value.
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

impl<T, N> FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  /// Returns the maximum number of elements this vector can hold.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U16;
  ///
  /// let mut vec: GenericVec<i32, U16> = GenericVec::new();
  /// let frozen = vec.freeze();
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
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// let frozen = vec.freeze();
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
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// let frozen = vec.freeze();
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
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U2;
  ///
  /// let mut vec: GenericVec<i32, U2> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// let frozen = vec.freeze();
  /// assert!(frozen.is_full());
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.inner.is_full()
  }

  /// Returns an iterator over `&T`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// vec.push(3);
  /// let frozen = vec.freeze();
  ///
  /// let sum: i32 = frozen.iter().sum();
  /// assert_eq!(sum, 6);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn iter(&self) -> core::slice::Iter<'_, T> {
    self.inner.iter()
  }

  /// Returns a slice of initialized values.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// vec.push(2);
  /// let frozen = vec.freeze();
  ///
  /// assert_eq!(frozen.as_slice(), &[1, 2]);
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_slice(&self) -> &[T] {
    self.inner.as_slice()
  }

  /// Returns a pointer to the first element.
  ///
  /// # Examples
  ///
  /// ```rust
  /// # {
  /// use logosky::utils::{GenericVec, typenum};
  /// use typenum::U4;
  ///
  /// let mut vec: GenericVec<i32, U4> = GenericVec::new();
  /// vec.push(1);
  /// let frozen = vec.freeze();
  ///
  /// let ptr = frozen.as_ptr();
  /// unsafe {
  ///     assert_eq!(*ptr, 1);
  /// }
  /// # }
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn as_ptr(&self) -> *const T {
    self.inner.as_ptr()
  }
}

impl<T, I, N> core::ops::Index<I> for FrozenGenericVec<T, N>
where
  I: core::slice::SliceIndex<[T]>,
  N: ArrayLength,
{
  type Output = I::Output;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn index(&self, index: I) -> &Self::Output {
    &self.inner[index]
  }
}

impl<T: PartialEq, N> PartialEq for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn eq(&self, other: &Self) -> bool {
    self.inner == other.inner
  }
}

impl<T: Eq, N> Eq for FrozenGenericVec<T, N> where N: ArrayLength {}

impl<T: PartialOrd, N> PartialOrd for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
    self.inner.partial_cmp(&other.inner)
  }
}

impl<T: Ord, N> Ord for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn cmp(&self, other: &Self) -> core::cmp::Ordering {
    self.inner.cmp(&other.inner)
  }
}

impl<T: core::hash::Hash, N> core::hash::Hash for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
    self.inner.hash(state);
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

impl<T, N> IntoIterator for FrozenGenericVec<T, N>
where
  N: ArrayLength,
{
  type Item = T;
  type IntoIter = GenericVecIter<T, N>;

  #[cfg_attr(not(tarpaulin), inline(always))]
  fn into_iter(self) -> Self::IntoIter {
    self.inner.into_iter()
  }
}

impl<T, N> GenericVec<T, N>
where
  N: ArrayLength,
{
  /// Freeze this `GenericVec` into an immutable `FrozenGenericVec`.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn freeze(self) -> FrozenGenericVec<T, N> {
    FrozenGenericVec { inner: self }
  }
}
