use core::ops::Range;

pub use positioned_char::*;
pub use unexpected_end::*;
pub use unexpected_lexeme::*;

/// Trackers for preventing infinite recursion in parsers.
pub mod recursion_tracker;
/// A token tracker for tracking tokens in a lexer.
pub mod token_tracker;
/// A tracker for tracking recursion depth and tokens.
pub mod tracker;

/// A module for custom comparing traits.
pub mod cmp;
/// A module for displaying in a human-friendly way.
pub mod human_display;
/// A module for displaying in SDL.
pub mod sdl_display;
/// A module for displaying in syntax trees.
pub mod syntax_tree_display;

pub use to_equivalent::*;

mod to_equivalent;

/// A module for container types with small size optimizations.
#[cfg(feature = "smallvec")]
#[cfg_attr(docsrs, doc(cfg(feature = "smallvec")))]
pub mod container;

mod positioned_char;
mod unexpected_end;
mod unexpected_lexeme;

/// A simple span just contains start and end position.
///
/// The structure is the same as [`Range<usize>`], but with more friendly methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
  start: usize,
  end: usize,
}

impl chumsky::span::Span for Span {
  type Context = ();

  type Offset = usize;

  #[inline(always)]
  fn new(_: Self::Context, range: Range<Self::Offset>) -> Self {
    Self::new(range.start, range.end)
  }

  #[inline(always)]
  fn context(&self) -> Self::Context {}

  #[inline(always)]
  fn start(&self) -> Self::Offset {
    self.start
  }

  #[inline(always)]
  fn end(&self) -> Self::Offset {
    self.end
  }
}

impl Span {
  /// Create a new span.
  ///
  /// ## Panics
  ///
  /// Panics if `end < start`.
  #[inline]
  pub const fn new(start: usize, end: usize) -> Self {
    assert!(end >= start, "end must be greater than or equal to start");
    Self { start, end }
  }

  /// Try to create a new span.
  ///
  /// Returns `None` if `end < start`.
  #[inline]
  pub const fn try_new(start: usize, end: usize) -> Option<Self> {
    if end >= start {
      Some(Self { start, end })
    } else {
      None
    }
  }

  /// Bump the start of the span by `n`.
  ///
  /// ## Panics
  ///
  /// Panics if `self.start + n > self.end`.
  #[inline]
  pub const fn bump_start(&mut self, n: usize) -> &mut Self {
    self.start += n;
    assert!(
      self.start <= self.end,
      "start must be less than or equal to end"
    );
    self
  }

  /// Bump the end of the span by `n`.
  #[inline]
  pub const fn bump_end(&mut self, n: usize) -> &mut Self {
    self.end += n;
    self
  }

  /// Bump the start and the end of the span by `n`.
  #[inline]
  pub const fn bump_span(&mut self, n: usize) -> &mut Self {
    self.start += n;
    self.end += n;
    self
  }

  /// Set the start of the span, returning a mutable reference to self.
  #[inline]
  pub const fn set_start(&mut self, start: usize) -> &mut Self {
    self.start = start;
    self
  }

  /// Set the end of the span, returning a mutable reference to self.
  #[inline]
  pub const fn set_end(&mut self, end: usize) -> &mut Self {
    self.end = end;
    self
  }

  /// Set the start of the span, returning self.
  #[inline]
  pub const fn with_start(mut self, start: usize) -> Self {
    self.start = start;
    self
  }

  /// Set the end of the span, returning self.
  #[inline]
  pub const fn with_end(mut self, end: usize) -> Self {
    self.end = end;
    self
  }

  /// Get the start of the span.
  #[inline]
  pub const fn start(&self) -> usize {
    self.start
  }

  /// Get the mutable reference to the start of the span.
  #[inline]
  pub const fn start_mut(&mut self) -> &mut usize {
    &mut self.start
  }

  /// Get the end of the span.
  #[inline]
  pub const fn end(&self) -> usize {
    self.end
  }

  /// Get the mutable reference to the end of the span.
  #[inline]
  pub const fn end_mut(&mut self) -> &mut usize {
    &mut self.end
  }

  /// Get the length of the span.
  #[inline]
  pub const fn len(&self) -> usize {
    self.end - self.start
  }

  /// Check if the span is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.start == self.end
  }

  /// Returns a range covering the span.
  #[inline]
  pub const fn range(&self) -> Range<usize> {
    self.start..self.end
  }
}

impl From<Range<usize>> for Span {
  #[inline]
  fn from(range: Range<usize>) -> Self {
    Self::new(range.start, range.end)
  }
}

impl From<Span> for Range<usize> {
  #[inline]
  fn from(span: Span) -> Self {
    span.start..span.end
  }
}

/// A spanned value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Spanned<D> {
  /// The span of the data.
  pub span: Span,
  /// The spanned data.
  pub data: D,
}

impl<D> AsRef<Span> for Spanned<D> {
  #[inline(always)]
  fn as_ref(&self) -> &Span {
    self.span()
  }
}

impl<D> AsSpan<Span> for Spanned<D> {
  #[inline(always)]
  fn as_span(&self) -> &Span {
    AsRef::as_ref(self)
  }
}

impl<D> IntoSpan<Span> for Spanned<D> {
  #[inline(always)]
  fn into_span(self) -> Span {
    self.span
  }
}

impl<D> core::ops::Deref for Spanned<D> {
  type Target = D;

  #[inline(always)]
  fn deref(&self) -> &Self::Target {
    &self.data
  }
}

impl<D> core::ops::DerefMut for Spanned<D> {
  #[inline(always)]
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut self.data
  }
}

impl<D> core::fmt::Display for Spanned<D>
where
  D: core::fmt::Display,
{
  #[inline]
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    self.data.fmt(f)
  }
}

impl<D> IntoComponents for Spanned<D> {
  type Components = (Span, D);

  #[inline]
  fn into_components(self) -> Self::Components {
    (self.span, self.data)
  }
}

impl<D> Spanned<D> {
  /// Create a new spanned value.
  #[inline]
  pub const fn new(span: Span, data: D) -> Self {
    Self { span, data }
  }

  /// Get a reference to the span.
  #[inline]
  pub const fn span(&self) -> &Span {
    &self.span
  }

  /// Get a mutable reference to the span.
  #[inline]
  pub const fn span_mut(&mut self) -> &mut Span {
    &mut self.span
  }

  /// Get a reference to the data.
  #[inline]
  pub const fn data(&self) -> &D {
    &self.data
  }

  /// Get a mutable reference to the data.
  #[inline]
  pub const fn data_mut(&mut self) -> &mut D {
    &mut self.data
  }

  /// Returns a reference to the span and data.
  #[inline]
  pub const fn as_ref(&self) -> Spanned<&D> {
    Spanned {
      span: self.span,
      data: &self.data,
    }
  }

  /// Consume the spanned value and return the data.
  #[inline]
  pub fn into_data(self) -> D {
    self.data
  }

  /// Decompose the spanned value into its span and data.
  #[inline]
  pub fn into_components(self) -> (Span, D) {
    (self.span, self.data)
  }
}

/// Enables accessing the source span of a parsed element.
///
/// This trait provides a way to retrieve the span information associated with
/// a parsed element without taking ownership of the element itself. This is
/// useful for scenarios where you need to reference the location of the element
/// in the source input, such as for error reporting or diagnostics.
///
/// ## Usage Patterns
/// Common scenarios for using this trait:
/// - **Error reporting**: Attaching span information to error messages
/// - **Diagnostics**: Highlighting source locations in IDEs or tools
/// - **Logging**: Recording where certain elements were parsed from
/// - **Analysis**: Performing source-based analysis or transformations
///
/// ## Implementation Notes
///
/// Implementing types should ensure that:
///   - The returned span is accurate and corresponds to the element's location in the source
///   - The method is efficient and does not involve unnecessary allocations or computations
///   - The trait is implemented for all relevant types
///   - The span information is preserved during parsing and transformations
///   - The implementation is consistent with other span-related traits
///   - The method is efficient (ideally zero-cost)
///   - The returned reference is valid for the lifetime of the element
pub trait AsSpan<Span> {
  /// Consumes this element and returns the owned source span.
  ///
  /// This method takes ownership of the element and extracts its span information
  /// as an owned value. This is useful when you need to transfer ownership of
  /// the span data to another data structure or when the element itself is no
  /// longer needed but the location information should be preserved.
  fn as_span(&self) -> &Span;
}

/// Enables consuming a parsed element to extract its source span.
///
/// This trait provides a way to take ownership of the span information from
/// a parsed element, which is useful when the element itself is no longer
/// needed but the span data should be preserved or transferred to another
/// data structure.
///
/// ## Usage Patterns
///
/// Common scenarios for using this trait:
/// - **AST construction**: Building higher-level AST nodes that need owned spans
/// - **Error collection**: Gathering span information for batch error reporting
/// - **Transformation**: Converting between different representations while preserving location
/// - **Optimization**: Avoiding clones when transferring ownership is acceptable
///
/// ## Implementation Notes
///
/// Implementing types should ensure that:
/// - The returned span is equivalent to what `AsSpan::spanned()` would return
/// - All span information is preserved during the conversion
/// - The conversion is efficient (ideally zero-cost)
pub trait IntoSpan<Span>: AsSpan<Span> {
  /// Consumes this element and returns the owned source span.
  ///
  /// This method takes ownership of the element and extracts its span information
  /// as an owned value. This is useful when you need to transfer ownership of
  /// the span data to another data structure or when the element itself is no
  /// longer needed but the location information should be preserved.
  fn into_span(self) -> Span;
}

/// Enables destructuring a parsed element into its constituent components.
///
/// This trait provides a way to break down complex parsed elements into their
/// individual parts, taking ownership of each component. This is particularly
/// useful for transformation, analysis, or when building different representations
/// of the parsed data.
///
/// ## Design Philosophy
///
/// The trait uses an associated type rather than generic parameters to ensure
/// that each implementing type has exactly one way to be decomposed. This provides
/// type safety and makes the interface predictable for consumers.
///
/// ## Usage Patterns
///
/// Common scenarios for using this trait:
/// - **AST transformation**: Converting parsed elements into different AST representations
/// - **Analysis**: Extracting specific components for validation or processing
/// - **Serialization**: Breaking down elements for custom serialization formats
/// - **Testing**: Accessing individual components for detailed assertions
///
/// ## Examples
///
/// ```rust,ignore
/// // Extracting components for transformation
/// let float_value: FloatValue<&str, SimpleSpan> = parse_float("3.14e-2")?;
/// let (span, int_part, frac_part, exp_part) = float_value.into_components();
///
/// // Building a custom representation
/// let custom_float = CustomFloat {
///     location: span,
///     integer: int_part,
///     fractional: frac_part,
///     exponent: exp_part,
/// };
///
/// // Component analysis
/// let int_literal: IntValue<&str, SimpleSpan> = parse_int("-42")?;
/// let (span, sign, digits) = int_literal.into_components();
///
/// if sign.is_some() {
///     println!("Found negative integer at {:?}", span);
/// }
/// ```
///
/// ## Implementation Guidelines
///
/// When implementing this trait:
/// - Include all meaningful components of the parsed element
/// - Order components logically (typically: span first, then sub-components in source order)
/// - Use tuples for simple decomposition, custom structs for complex cases
/// - Ensure the decomposition is complete (no information loss)
/// - Document the component structure clearly
///
/// ## Component Ordering Convention
///
/// To maintain consistency across implementations, follow this ordering:
/// 1. **Overall span**: The span covering the entire element
/// 2. **Required components**: Core parts that are always present
/// 3. **Optional components**: Parts that may or may not be present
/// 4. **Sub-elements**: Nested parsed elements in source order
pub trait IntoComponents {
  /// The tuple or struct type containing the decomposed components.
  ///
  /// This associated type defines the structure returned by `into_components()`.
  /// It should include all meaningful parts of the parsed element in a logical
  /// order that makes sense for the specific element type.
  type Components;

  /// Consumes this element and returns its constituent components.
  ///
  /// This method breaks down the parsed element into its individual parts,
  /// providing owned access to each component. The exact structure of the
  /// returned components is defined by the `Components` associated type.
  fn into_components(self) -> Self::Components;
}
