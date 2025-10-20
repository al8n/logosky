pub use logos::{Source, source::Chunk};

#[cfg(feature = "bytes")]
mod bytes;

#[cfg(feature = "bstr")]
mod bstr;

#[cfg(feature = "hipstr")]
mod hipstr;

/// A transparent wrapper for custom source types to work around Logos orphan rule limitations.
///
/// `CustomSource` solves a specific problem when using types like [`bytes::Bytes`] or
/// [`bstr::BStr`] as lexer sources. These types implement `Deref<Target = [u8]>`, but
/// Rust's orphan rules prevent LogoSky from implementing `logos::Source` for them directly
/// (since both the trait and the type are defined in external crates).
///
/// By wrapping these types in `CustomSource`, you can use them as Logos sources without
/// any runtime overhead - the wrapper is completely transparent thanks to `#[repr(transparent)]`.
///
/// # The Problem This Solves
///
/// Without `CustomSource`, you might encounter errors like:
///
/// ```text
/// error[E0119]: conflicting implementations of trait `logos::Source`
///   --> src/lib.rs:10:1
///    |
/// 10 | impl Source for bytes::Bytes { ... }
///    | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///    |
///    = note: conflicting implementation in crate `bytes`:
///            - impl<T> Deref for Bytes where T: Deref<Target = [u8]>;
/// ```
///
/// `CustomSource` wraps the type to create a distinct type that LogoSky *can* implement traits for.
///
/// # Zero-Cost Abstraction
///
/// This wrapper is completely free at runtime:
/// - No memory overhead (transparent representation)
/// - No indirection (direct access to inner value)
/// - All methods are `#[inline(always)]`
/// - The wrapper is optimized away by the compiler
///
/// # Supported Types
///
/// LogoSky provides implementations for:
///
/// - **`bytes::Bytes`** (with `bytes` feature): Zero-copy byte buffers
/// - **`bstr::BStr`** (with `bstr` feature): Byte string slices
/// - **`hipstr::HipStr`** (with `hipstr` feature): Inline/heap strings
///
/// # Examples
///
/// ## Using with bytes::Bytes
///
/// ```rust,ignore
/// use bytes::Bytes;
/// use logos::Logos;
/// use logosky::source::CustomSource;
///
/// #[derive(Logos, Debug, Clone, Copy)]
/// #[logos(source = CustomSource<Bytes>)]
/// enum Token {
///     #[regex(b"[0-9]+")]
///     Number,
///
///     #[regex(b"[a-zA-Z]+")]
///     Word,
/// }
///
/// let input: CustomSource<Bytes> = Bytes::from_static(b"42 hello").into();
/// let mut lexer = Token::lexer(&input);
///
/// assert!(matches!(lexer.next(), Some(Ok(Token::Number))));
/// assert!(matches!(lexer.next(), Some(Ok(Token::Word))));
/// ```
///
/// ## Zero-Cost Conversions
///
/// ```rust,ignore
/// use bytes::Bytes;
/// use logosky::source::CustomSource;
///
/// let bytes = Bytes::from_static(b"hello");
///
/// // Convert to CustomSource (zero cost)
/// let source: CustomSource<Bytes> = bytes.into();
///
/// // Access the inner value (zero cost)
/// let inner: &Bytes = source.as_inner();
///
/// // Get it back (zero cost)
/// let bytes_again: Bytes = source.into_inner();
/// ```
///
/// ## Using with References
///
/// ```rust,ignore
/// use bytes::Bytes;
/// use logosky::source::CustomSource;
///
/// let bytes = Bytes::from_static(b"data");
///
/// // Create CustomSource from a reference without cloning
/// let source_ref: &CustomSource<Bytes> = CustomSource::from_ref(&bytes);
///
/// // Use it directly
/// process_source(source_ref);
/// ```
///
/// # API Overview
///
/// - **`from_ref(&S) -> &CustomSource<S>`**: Create from reference (zero-cost transmute)
/// - **`from_mut(&mut S) -> &mut CustomSource<S>`**: Create from mutable reference
/// - **`as_inner(&self) -> &S`**: Access inner value
/// - **`into_inner(self) -> S`**: Extract inner value
/// - **`From<S>`**: Convert from the wrapped type
///
/// # When to Use This
///
/// Use `CustomSource` when:
/// - You want to use `bytes::Bytes`, `bstr::BStr`, or `hipstr::HipStr` as a Logos source
/// - You're getting orphan rule errors about conflicting Source implementations
/// - You need zero-copy lexing with specialized buffer types
///
/// You don't need `CustomSource` for:
/// - Standard string slices (`&str`) - these work directly with Logos
/// - Byte slices (`&[u8]`) - these also work directly
/// - Owned strings (`String`) - use `&str` instead
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct CustomSource<S: ?Sized>(S);

impl<S, T> AsRef<T> for CustomSource<S>
where
  S: AsRef<T> + ?Sized,
  T: ?Sized,
{
  #[inline(always)]
  fn as_ref(&self) -> &T {
    self.0.as_ref()
  }
}

impl<S, T> AsMut<T> for CustomSource<S>
where
  S: AsMut<T> + ?Sized,
  T: ?Sized,
{
  #[inline(always)]
  fn as_mut(&mut self) -> &mut T {
    self.0.as_mut()
  }
}

impl<S> From<S> for CustomSource<S> {
  #[inline(always)]
  fn from(s: S) -> Self {
    Self(s)
  }
}

impl<S: ?Sized> CustomSource<S> {
  /// Creates a `CustomSource` reference from a reference to the wrapped type.
  ///
  /// This is a zero-cost operation that reinterprets a reference to `S` as a reference
  /// to `CustomSource<S>`. This is safe because `CustomSource` is `#[repr(transparent)]`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bytes::Bytes;
  /// use logosky::source::CustomSource;
  ///
  /// let bytes = Bytes::from_static(b"hello");
  /// let source_ref: &CustomSource<Bytes> = CustomSource::from_ref(&bytes);
  /// ```
  ///
  /// # Use Case
  ///
  /// This is particularly useful when you need to pass a borrowed value to a function
  /// expecting `&CustomSource<S>` without cloning or moving the original value.
  #[inline(always)]
  pub const fn from_ref(source: &S) -> &Self {
    // Safety:
    // The cast is safe because `CustomSource` is a transparent wrapper.
    unsafe { &*(source as *const S as *const Self) }
  }

  /// Creates a mutable `CustomSource` reference from a mutable reference to the wrapped type.
  ///
  /// This is a zero-cost operation that reinterprets a mutable reference to `S` as a
  /// mutable reference to `CustomSource<S>`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use bytes::Bytes;
  /// use logosky::source::CustomSource;
  ///
  /// let mut bytes = Bytes::from_static(b"data");
  /// let source_mut: &mut CustomSource<Bytes> = CustomSource::from_mut(&mut bytes);
  /// ```
  #[inline(always)]
  pub const fn from_mut(source: &mut S) -> &mut Self {
    // Safety:
    // The cast is safe because `CustomSource` is a transparent wrapper.
    unsafe { &mut *(source as *mut S as *mut Self) }
  }

  /// Returns a `CustomSource` wrapping a reference to the inner value.
  ///
  /// This creates a new `CustomSource<&S>` that borrows the inner data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::source::CustomSource;
  /// use bytes::Bytes;
  ///
  /// let source = CustomSource::from(Bytes::from_static(b"hello"));
  /// let borrowed: CustomSource<&Bytes> = source.as_ref();
  /// ```
  #[inline(always)]
  pub const fn as_ref(&self) -> CustomSource<&S> {
    CustomSource(&self.0)
  }

  /// Returns a `CustomSource` wrapping a mutable reference to the inner value.
  ///
  /// This creates a new `CustomSource<&mut S>` that mutably borrows the inner data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::source::CustomSource;
  /// use bytes::Bytes;
  ///
  /// let mut source = CustomSource::from(Bytes::from_static(b"hello"));
  /// let mut_borrowed: CustomSource<&mut Bytes> = source.as_mut();
  /// ```
  #[inline(always)]
  pub fn as_mut(&mut self) -> CustomSource<&mut S> {
    CustomSource(&mut self.0)
  }

  /// Returns a reference to the inner wrapped value.
  ///
  /// This is the primary way to access the wrapped value when you need to call
  /// methods specific to the inner type.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::source::CustomSource;
  /// use bytes::Bytes;
  ///
  /// let source = CustomSource::from(Bytes::from_static(b"hello world"));
  /// let inner: &Bytes = source.as_inner();
  ///
  /// // Can now call Bytes-specific methods
  /// assert_eq!(inner.len(), 11);
  /// ```
  #[inline(always)]
  pub const fn as_inner(&self) -> &S {
    &self.0
  }

  /// Returns a mutable reference to the inner wrapped value.
  ///
  /// This allows you to modify the wrapped value directly.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::source::CustomSource;
  /// use bytes::BytesMut;
  ///
  /// let mut source = CustomSource::from(BytesMut::from("hello"));
  /// let inner: &mut BytesMut = source.as_inner_mut();
  ///
  /// // Modify the inner value
  /// inner.extend_from_slice(b" world");
  /// ```
  #[inline(always)]
  pub fn as_inner_mut(&mut self) -> &mut S {
    &mut self.0
  }

  /// Consumes the `CustomSource` and returns the wrapped value.
  ///
  /// This is a zero-cost operation that unwraps the inner value.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use logosky::source::CustomSource;
  /// use bytes::Bytes;
  ///
  /// let source = CustomSource::from(Bytes::from_static(b"hello"));
  /// let bytes: Bytes = source.into_inner();
  ///
  /// assert_eq!(&bytes[..], b"hello");
  /// ```
  #[inline(always)]
  pub fn into_inner(self) -> S
  where
    S: Sized,
  {
    self.0
  }
}
