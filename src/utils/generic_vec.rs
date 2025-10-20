//! Bounded, stack-allocated vector implementations for no-alloc environments.
//!
//! This module provides `GenericVec`, a fixed-capacity vector that drops elements
//! when full instead of allocating more memory. Two implementations are provided:
//!
//! - **Const-generic** (default): Uses `const N: usize` for capacity specification
//! - **Type-level** (with `generic-array` feature): Uses `typenum` for type-level capacity
//!
//! The implementation is chosen at compile time based on feature flags.
//!
//! # Feature Flags
//!
//! - Without `generic-array`: Uses const-generic implementation with `const N: usize`
//! - With `generic-array`: Uses type-level implementation with `generic_array::ArrayLength`
//!
//! # Design Philosophy
//!
//! This vector is designed for **error collection in parsers** running in no-alloc environments.
//! The key insight: it's better to collect and report the first N errors than to:
//! - Panic on the first error (loses context)
//! - Require allocation (not available in no_std)
//! - Grow unboundedly (DoS risk)
//!
//! # Use Cases
//!
//! ## Parser Error Collection
//!
//! ```rust
//! # #[cfg(not(feature = "generic-array"))] {
//! use logosky::utils::GenericVec;
//!
//! fn validate_input(input: &[&str]) -> Result<(), GenericVec<String, 10>> {
//!     let mut errors = GenericVec::new();
//!
//!     for (i, line) in input.iter().enumerate() {
//!         if line.is_empty() {
//!             errors.push(format!("Line {}: empty", i));
//!         }
//!         if line.len() > 100 {
//!             errors.push(format!("Line {}: too long", i));
//!         }
//!     }
//!
//!     if errors.is_empty() {
//!         Ok(())
//!     } else {
//!         Err(errors)
//!     }
//! }
//! # }
//! ```
//!
//! ## Const-Generic Version (Default)
//!
//! ```rust
//! # #[cfg(not(feature = "generic-array"))] {
//! use logosky::utils::GenericVec;
//!
//! let mut vec: GenericVec<i32, 8> = GenericVec::new();
//! vec.push(1);
//! vec.push(2);
//! assert_eq!(vec.len(), 2);
//! # }
//! ```
//!
//! ## Type-Level Version (with generic-array feature)
//!
//! ```rust
//! # #[cfg(feature = "generic-array")] {
//! use logosky::utils::{GenericVec, typenum};
//! use typenum::U8;
//!
//! let mut vec: GenericVec<i32, U8> = GenericVec::new();
//! vec.push(1);
//! vec.push(2);
//! assert_eq!(vec.len(), 2);
//! # }
//! ```

// Conditionally include the appropriate implementation
#[cfg(not(feature = "generic-array"))]
mod const_generic;
#[cfg(not(feature = "generic-array"))]
pub use const_generic::GenericVec;

#[cfg(feature = "generic-array")]
#[cfg_attr(docsrs, doc(cfg(feature = "generic-array")))]
mod type_level;
#[cfg(feature = "generic-array")]
#[cfg_attr(docsrs, doc(cfg(feature = "generic-array")))]
pub use type_level::GenericVec;
