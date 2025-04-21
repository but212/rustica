//! # Comonad
//!
//! This module provides the `Comonad` trait which represents the categorical dual of a monad.
//! While monads wrap values in a context and sequence computations that produce values,
//! comonads extract values from a context and sequence computations that consume contexts.
//!
//! ## Examples
//!
//! The `Comonad` trait enables powerful patterns for working with contextualized values:
//!
//! ```rust
//! use rustica::traits::comonad::Comonad;
//!
//! // Using Option<T> as a comonad
//! let value: Option<i32> = Some(42);
//!
//! // Extract the value from the context
//! assert_eq!(value.extract(), 42);
//!
//! // Extend a computation over the context
//! let doubled = value.extend(|opt| opt.extract() * 2);
//! assert_eq!(doubled, Some(84));
//!
//! // Using nested comonadic operations
//! let result = value
//!     .extend(|opt| opt.extract() * 3)  // multiply by 3
//!     .extend(|opt| opt.extract() + 10); // add 10 to the result
//! assert_eq!(result, Some(136));
//! ```
//!
//! ## Mathematical Definition
//!
//! In category theory, a comonad on a category C consists of:
//! - An endofunctor T: C → C
//! - A natural transformation ε: T → Id (called `extract`)
//! - A natural transformation δ: T → T² (called `duplicate`)
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
//! ## Common Use Cases
//!
//! Comonads are particularly useful for:
//!
//! 1. **Data with Context** - When you need to process values while considering their surroundings
//!
//! 2. **Stateful Transformations** - When transformations depend on the current state
//!
//! 3. **Bidirectional Computations** - When you need to both inject and extract information
//!
//! ## Relationship with Other Functional Traits
//!
//! - **Monad**: Comonads are the categorical dual of monads. While monads let you sequence
//!   computations that produce contexts, comonads let you sequence computations that consume contexts.
//!
//! - **Functor**: Both monads and comonads are functors. Comonads add the ability to extract
//!   values from and duplicate contexts.
//!

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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::id::Id;
    ///
    /// let id: Id<i32> = Id::new(42);
    /// assert_eq!(id.extract(), 42);
    /// ```
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe: Maybe<i32> = Maybe::Just(123);
    /// assert_eq!(maybe.extract(), 123);
    /// ```
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
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe: Maybe<i32> = Maybe::Just(5);
    /// let result = maybe.extend(|x| x.extract() + 3);
    /// assert_eq!(result.extract(), 8);
    /// ```
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U;

    /// Duplicates the context of a comonad.
    ///
    /// This operation creates a new layer of context, where each position in the
    /// result contains the sub-context focused at that position.
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
    /// let _duplicated = id.duplicate();
    /// ```
    ///
    /// ```rust
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe: Maybe<i32> = Maybe::Just(10);
    /// // The duplicate method returns the original context wrapped in another context layer
    /// let _duplicated = maybe.duplicate();
    /// ```
    fn duplicate(&self) -> Self;
}

impl<A: Clone> Comonad for Option<A> {
    fn extract(&self) -> A {
        match self {
            Some(a) => a.clone(),
            None => panic!("Called `extract` on a `None` value"),
        }
    }

    fn duplicate(&self) -> Self {
        self.clone()
    }

    fn extend<U, F>(&self, f: F) -> Option<U>
    where
        F: Fn(&Self) -> U,
    {
        self.as_ref().map(|_| f(self))
    }
}

impl<T: Clone, E: Clone + std::fmt::Debug> Comonad for Result<T, E> {
    fn extract(&self) -> T {
        match self {
            Ok(t) => t.clone(),
            Err(_) => panic!("Called `extract` on an `Err` value"),
        }
    }

    fn duplicate(&self) -> Self {
        self.clone()
    }

    fn extend<U, F>(&self, f: F) -> Result<U, E>
    where
        F: Fn(&Self) -> U,
    {
        match self {
            Ok(_) => Ok(f(self)),
            Err(e) => Err(e.clone()),
        }
    }
}
