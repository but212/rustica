//! # Comonad
//!
//! This module provides the `Comonad` trait which represents the categorical dual of a monad.
//! While monads wrap values in a context and sequence computations that produce values,
//! comonads extract values from a context and sequence computations that consume contexts.
//!
//! # Category Theory
//!
//! In category theory, the `extract` operation must be total (always succeed). This means
//! types like `Option` and `Result` are not valid comonads because `extract` cannot be
//! safely implemented for `None` or `Err` cases.
//!
//! ## Examples
//!
//! The `Comonad` trait enables powerful patterns for working with contextualized values:
//!
//! ```rust
//! use rustica::traits::comonad::Comonad;
//! use rustica::datatypes::id::Id;
//!
//! // Using Id<T> as a comonad (always safe)
//! let value: Id<i32> = Id::new(42);
//!
//! // Extract the value from the context (always succeeds)
//! assert_eq!(value.extract(), 42);
//!
//! // Extend a computation over the context
//! let doubled = value.extend(|id| id.extract() * 2);
//! assert_eq!(doubled.extract(), 84);
//!
//! // Using nested comonadic operations
//! let result = value
//!     .extend(|id| id.extract() * 3)  // multiply by 3
//!     .extend(|id| id.extract() + 10); // add 10 to the result
//! assert_eq!(result.extract(), 136);
//! ```
//!
//! ## Mathematical Definition
//!
//! In category theory, a comonad on a category C consists of:
//! - An endofunctor W: C → C
//! - A natural transformation ε: W → Id (called `extract`) - **MUST BE TOTAL**
//! - A natural transformation δ: W → W² (called `duplicate`)
//!
//! ## Laws
//!
//! A valid comonad must satisfy these laws:
//!
//! 1. **Left Identity**: `extend(extract)(w) = w`  
//!    Extending a comonad with extract returns the original comonad.
//!
//! 2. **Right Identity**: `extract(extend(f)(w)) = f(w)`  
//!    Extracting from an extended comonad equals applying the function directly.
//!
//! 3. **Associativity**: `extend(f)(extend(g)(w)) = extend(|x| f(extend(g)(x)))(w)`  
//!    The order of extending computations doesn't matter.
//!
//! ## Totality Requirement
//!
//! The `extract` operation must be total (never fail). This is a fundamental requirement
//! of category theory. Types where extraction can fail (like `Option` or `Result`) are
//! not valid comonads.
//!
//! ## Common Use Cases
//!
//! Comonads are particularly useful for:
//!
//! 1. **Data with Context** - When you need to process values while considering their surroundings
//!    (e.g., cellular automata, image processing with neighborhoods)
//!
//! 2. **Stateful Transformations** - When transformations depend on the current state
//!    (e.g., traced computations, store-based computations)
//!
//! 3. **Non-empty Structures** - When you need guaranteed extraction from collections
//!    (e.g., non-empty lists, streams, zippers)
//!
//! 4. **UI Components** - When components need access to their environment/context
//!    (e.g., React-like component trees with context)
//!
//! ## Safe Comonad Types
//!
//! Examples of types that can safely implement Comonad:
//! - `Id<T>` (Identity)
//! - `NonEmpty<Vec<T>>` (Non-empty vectors)
//! - `Stream<T>` (Infinite streams)
//! - `Zipper<T>` (List zippers with focus)
//! - `Store<S, A>` (Store comonad)
//! - `Traced<M, A>` where M is a monoid
//!
//! ## Relationship with Other Functional Traits
//!
//! - **Monad**: Comonads are the categorical dual of monads. While monads let you sequence
//!   computations that produce contexts, comonads let you sequence computations that consume contexts.
//!
//! - **Functor**: Both monads and comonads are functors. Comonads add the ability to extract
//!   values from and duplicate contexts.
//!

use crate::traits::functor::Functor;

/// A marker trait for types that can safely implement Comonad.
///
/// This trait serves as documentation and a compile-time check that a type
/// can provide a total `extract` operation.
pub trait SafeComonad {
    /// Returns true if extract is guaranteed to never fail for this type.
    /// This should always return true for valid implementations.
    fn is_extract_total() -> bool {
        true
    }
}

/// A comonad is the categorical dual of a monad, providing operations to extract values from a context
/// and extend computations that consume contexts. While monads represent computations that add context,
/// comonads represent computations that can read from contexts.
///
/// # Category Theory Requirements
///
/// For a type to be a valid comonad, the `extract` operation must be total (always succeed).
/// This means types like `Option<T>` and `Result<T, E>` are NOT valid comonads because
/// `extract` cannot be safely implemented for `None` or `Err` cases.
///
/// Valid comonads include:
/// - `Id<T>` (Identity)
/// - Non-empty lists
/// - Streams
/// - Zippers
/// - Store comonads
///
/// Note: Comonads are independent of monads in category theory. They both extend Functor,
/// but a type can be a comonad without being a monad, and vice versa.
pub trait Comonad: Functor {
    /// Extracts the value from a comonadic context.
    ///
    /// This is dual to the `pure` operation in monads - while `pure` wraps a value in a context,
    /// `extract` retrieves a value from a context.
    ///
    /// # Category Theory
    ///
    /// This operation corresponds to the counit (ε: W A → A) of the comonad.
    /// It must be total (always succeed) for the type to be a valid comonad.
    ///
    /// # Returns
    ///
    /// The value contained in the comonad (always succeeds)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::id::Id;
    ///
    /// let id: Id<i32> = Id::new(42);
    /// assert_eq!(id.extract(), 42); // Always safe
    /// ```
    fn extract(&self) -> Self::Source;

    /// Extends a computation over a comonadic context.
    ///
    /// While monadic bind (>>=) allows you to sequence computations that produce contexts,
    /// extend allows you to sequence computations that consume contexts.
    ///
    /// # Category Theory
    ///
    /// This operation is derived from duplicate and fmap:
    /// `extend f = fmap f . duplicate`
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the result
    /// * `F`: The type of the function that consumes the comonadic context
    ///
    /// # Arguments
    ///
    /// * `f`: A function that takes a reference to the comonad and produces a value
    ///
    /// # Returns
    ///
    /// The result of applying the function to the comonadic context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::id::Id;
    ///
    /// let id: Id<i32> = Id::new(10);
    /// let result = id.extend(|x| x.extract() * 2);
    /// assert_eq!(result.extract(), 20);
    /// ```
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U,
        U: Clone;

    /// Duplicates the context of a comonad.
    ///
    /// This operation creates a new layer of context, where each position in the
    /// result contains the sub-context focused at that position.
    ///
    /// # Category Theory
    ///
    /// This corresponds to the comultiplication (δ: W A → W (W A)) of the comonad.
    /// It must satisfy the comonad laws together with extract.
    ///
    /// # Returns
    ///
    /// A new comonad with duplicated context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::id::Id;
    ///
    /// let id: Id<i32> = Id::new(42);
    /// // The duplicate method returns the original context wrapped in another context layer
    /// let duplicated = id.duplicate();
    /// // For Id, duplicate is essentially the identity operation
    /// assert_eq!(duplicated.extract(), 42);
    /// ```
    fn duplicate(&self) -> Self;
}
