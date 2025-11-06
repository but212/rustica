//! # Identity Trait (Value Extraction Utility)
//!
//! **DEPRECATED: This trait is a design flaw and will be removed in a future version. 0.12.0**
//!
//! ## Why is this deprecated?
//!
//! 1. **Wrong abstraction**: This trait mixes "value extraction" with the name "Identity" (identity functor)
//! 2. **Unnecessary**: Standard Rust already provides `.unwrap()`, `.as_ref()`, etc.
//! 3. **Comonad overlap**: `Comonad::extract()` already provides proper categorical value extraction
//! 4. **Functor pollution**: Forces `Functor: Identity` dependency, which is categorically wrong
//!
//! ## Migration Guide
//!
//! **Instead of `Identity` methods, use:**
//! - `value()` → `unwrap()` or `expect("message")`
//! - `try_value()` → `as_ref()`
//! - `into_value()` → `unwrap()` or the value itself
//! - `try_into_value()` → `Some(self)` or the option itself
//! - For comonads → Use `Comonad::extract()`
//!
//! ## When to Use
//!
//! - `**Option<T>**`: For optional values that may or may not be present
//! - `**Result<T, E>**`: For computations that may fail
//! - **Wrapper types*`*: Simple wrapper types that hold a single value
//!
//! ## When NOT to Use
//!
//! - **Collections** (Vec, List): These hold multiple values, not a single extractable value
//! - **Identity functor**: Use `Id<T>` type with `Comonad` trait instead
//! - **Types with total extraction**: Use `Comonad` trait for proper categorical semantics
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::identity::Identity;
//!
//! // A simple wrapper type
//! struct Wrapper<T>(T);
//!
//! impl<T> HKT for Wrapper<T> {
//!     type Source = T;
//!     type Output<U> = Wrapper<U>;
//! }
//!
//! impl<T> Identity for Wrapper<T> {
//!     #[inline]
//!     fn value(&self) -> &Self::Source {
//!         &self.0
//!     }
//!     
//!     #[inline]
//!     fn into_value(self) -> Self::Source {
//!         self.0
//!     }
//! }
//!
//! // Using the Identity trait
//! let wrapped: Wrapper<i32> = Wrapper(42);
//! assert_eq!(*wrapped.value(), 42);
//!
//! // The identity function is now in utils::functions::id
//! // use rustica::id;
//! // assert_eq!(id(5), 5);
//! ```
//!
//! ## TODO: Future Improvements
//!
//! - **Extended Examples**: Add more examples showing integration with other functional traits
//! - **Performance Benchmarks**: Add documentation about performance characteristics
//! - **Implementation Guidelines**: Add guidelines for correctly implementing the trait
//! - **Type Safety**: Enhance documentation around type safety considerations
//! - **Additional Extensions**: Consider adding more utility methods to the `IdentityExt` trait

use crate::traits::hkt::HKT;

/// **DEPRECATED: Design flaw - will be removed in 0.12.0**
///
/// This trait is deprecated because:
/// - It's an unnecessary abstraction over standard methods (unwrap, as_ref)
/// - It conflicts with the "Identity functor" concept from category theory
/// - It overlaps with `Comonad::extract()`
/// - It forces a wrong dependency: `Functor: Identity`
///
/// # Migration
///
/// Use standard Rust methods or `Comonad::extract()`:
/// ```rust,ignore
/// // OLD (deprecated)
/// container.value()           // ❌
/// container.try_value()       // ❌
/// container.into_value()      // ❌
///
/// // NEW (correct)
/// container.unwrap()          // ✅
/// container.as_ref()          // ✅
/// comonad.extract()           // ✅ for comonads
/// ```
#[deprecated(
    since = "0.11.0",
    note = "Identity trait is a design flaw. Use unwrap(), as_ref(), or Comonad::extract() instead"
)]
pub trait Identity: HKT {
    /// Returns a reference to the contained value.
    ///
    /// # Panics
    ///
    /// This method may panic if the container doesn't contain a valid value.
    /// For a non-panicking alternative, use `try_value()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(*some_value.value(), 42);
    ///
    /// // This would panic:
    /// // let none_value: Option<i32> = None;
    /// // none_value.value(); // panics
    /// ```
    fn value(&self) -> &Self::Source;

    /// Returns a reference to the contained value, if available.
    ///
    /// This method is safer than `value()` as it returns an `Option`
    /// instead of potentially panicking.
    ///
    /// # Default Implementation
    ///
    /// By default, this calls `value()` and wraps the result in `Some`.
    /// Types that might not contain a value should override this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.try_value(), Some(&42));
    ///
    /// let none_value: Option<i32> = None;
    /// assert_eq!(none_value.try_value(), None);
    /// ```
    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        Some(self.value())
    }

    /// Consumes self and returns the contained value.
    ///
    /// # Panics
    ///
    /// This method may panic if the container doesn't contain a valid value.
    /// For a non-panicking alternative, use `try_into_value()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.into_value(), 42);
    ///
    /// // This would panic:
    /// // let none_value: Option<i32> = None;
    /// // none_value.into_value(); // panics
    /// ```
    fn into_value(self) -> Self::Source;

    /// Consumes self and returns the contained value, if available.
    ///
    /// This method is safer than `into_value()` as it returns an `Option`
    /// instead of potentially panicking.
    ///
    /// # Default Implementation
    ///
    /// By default, this method attempts to obtain the value using `into_value()`.
    /// Types that might not contain a value should override this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.try_into_value(), Some(42));
    ///
    /// let none_value: Option<i32> = None;
    /// assert_eq!(none_value.try_into_value(), None);
    /// ```
    #[inline]
    fn try_into_value(self) -> Option<Self::Source>
    where
        Self: Sized,
    {
        Some(self.into_value())
    }

    // NOTE: The id() function has been moved to `rustica::utils::functions::id`
    // It's now a standalone function available in the prelude:
    //
    //   use rustica::prelude::*;
    //   let x = id(42);  //
    //
    // This is the correct location for the identity morphism, as it's not
    // related to value extraction (the purpose of this deprecated trait).
}

// Standard Library Implementations

impl<T> Identity for Option<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.as_ref().expect("Option is None")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.as_ref()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.expect("Option is None")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self
    }
}

impl<T, E: Clone + std::fmt::Debug> Identity for Result<T, E> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.as_ref().expect("Result is Err")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.as_ref().ok()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.expect("Result is Err")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self.ok()
    }
}
