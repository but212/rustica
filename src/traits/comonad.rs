//! # Comonad
//!
//! This module provides the [`Comonad`] trait which represents the categorical dual of a monad.
//! While monads wrap values in a context and sequence computations that produce values,
//! comonads extract values from a context and sequence computations that consume contexts.
//!
//! ## Mathematical Definition
//!
//! In category theory, a comonad on a category C consists of:
//! - An endofunctor T: C → C
//! - A natural transformation ε: T → Id (`extract`)
//! - A natural transformation δ: T → T² (`duplicate`)
//!
//! ## Laws
//!
//! A valid comonad must satisfy these laws:
//!
//! 1. Left Identity:
//! ```text
//! extend(extract)(w) = w
//! ```
//! Extending a comonad with extract should return the original comonad.
//!
//! 2. Right Identity:
//! ```text
//! extract(extend(f)(w)) = f(w)
//! ```
//! Extracting from an extended comonad should be the same as applying the function directly.
//!
//! 3. Associativity:
//! ```text
//! extend(f)(extend(g)(w)) = extend(|x| f(extend(g)(x)))(w)
//! ```
//! The order of extending computations shouldn't matter.
//!
//! ## Common Use Cases
//!
//! The Comonad trait is commonly used in scenarios where:
//!
//! 1. **Cellular Automata**
//!    - Each cell needs access to its neighbors
//!    - The comonad represents the infinite grid
//!    - extend computes the next generation
//!
//! 2. **Image Processing**
//!    - Each pixel needs access to surrounding pixels
//!    - The comonad represents the image
//!    - extend applies filters or convolutions
//!
//! 3. **Sliding Windows**
//!    - Processing streams of data with context
//!    - The comonad represents the infinite stream
//!    - extend computes windowed aggregations
//!
//! ## Relationship with Other Functional Traits
//!
//! - **Monad**: Comonads are the categorical dual of monads. While monads let you sequence
//!   computations that produce contexts, comonads let you sequence computations that consume contexts.
//!
//! - **Functor**: Both monads and comonads are functors. Comonads add the ability to extract
//!   values from and duplicate contexts.
//!
//! ## TODO: Future Improvements
//!
//! - **Additional Implementations**: Add implementations for more data structures (e.g., streams, grids, trees)
//! - **Law Testing**: Add property-based tests to verify that implementations satisfy comonad laws
//! - **Zipper Implementation**: Add a Zipper data structure, which is a classic example of a comonad
//! - **Stream Implementation**: Implement an infinite stream data structure with comonad instance
//! - **Doctest Examples**: Add comprehensive examples that demonstrate comonad usage
//! - **Extension Methods**: Create a ComonadExt trait with additional utility methods
//! - **Store Comonad**: Implement the Store comonad which pairs a function with a focus point
//! - **Traced Comonad**: Implement the Traced comonad for executing computations with a trace of past values
//! - **Integration with Monad**: Explore deeper relationships between monads and comonads

use crate::traits::monad::Monad;

/// A comonad is the categorical dual of a monad, providing operations to extract values from a context
/// and extend computations that consume contexts. While monads represent computations that add context,
/// comonads represent computations that can read from contexts.
pub trait Comonad: Monad {
    /// Extracts the value from a comonadic context.
    ///
    /// This is dual to the `pure` operation in monads - while `pure` wraps a value in a context,
    /// `extract` retrieves a value from a context.
    ///
    /// # Returns
    ///
    /// The value contained in the comonad
    fn extract(&self) -> Self::Source;

    /// Extends a computation over a comonadic context.
    ///
    /// While monadic bind (>>=) allows you to sequence computations that produce contexts,
    /// extend allows you to sequence computations that consume contexts.
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
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U;

    /// Maps a function over the context of the comonad.
    ///
    /// This is similar to contravariant_map but operates on the context rather than the value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the result
    /// * `F`: The type of the function that produces a new context
    ///
    /// # Arguments
    ///
    /// * `f`: A function that takes a reference to U and produces a new comonadic context
    ///
    /// # Returns
    ///
    /// The result of mapping the function over the context
    fn comap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&U) -> Self;

    /// Duplicates the context of a comonad.
    ///
    /// This operation creates a new layer of context, where each position in the
    /// result contains the sub-context focused at that position.
    ///
    /// # Returns
    ///
    /// A new comonad with duplicated context
    fn duplicate(&self) -> Self;
}
