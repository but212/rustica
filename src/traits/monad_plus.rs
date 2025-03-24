//! # MonadPlus
//!
//! The `MonadPlus` module provides a trait definition for monads that support
//! choice operations, extending the basic Monad trait. It's similar to Alternative
//! in Haskell, but specifically for monads.
//!
//! MonadPlus adds two key operations:
//! - `mzero`: A monad that represents failure or an empty computation
//! - `mplus`: An operation to combine two monads of the same type
//!
//! # Laws
//!
//! For a valid MonadPlus implementation, the following laws should hold:
//!
//! 1. Identity: `mzero().mplus(&x) == x` and `x.mplus(&mzero()) == x`
//!    - Zero is a neutral element for mplus
//!
//! 2. Associativity: `a.mplus(&b).mplus(&c) == a.mplus(&b.mplus(&c))`
//!    - The mplus operation is associative
//!
//! 3. Left Zero: `mzero().bind(f) == mzero()`
//!    - Zero is annihilator for bind
//!
//! 4. Right Zero: `x.bind(|_| mzero()) == mzero()`
//!    - Zero is annihilator for bind in the other direction
//!
//! 5. Left Distribution: `a.mplus(&b).bind(f) == a.bind(f).mplus(&b.bind(f))`
//!    - Bind distributes over mplus
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::monad_plus::MonadPlus;
//! use rustica::traits::monad::Monad;
//!
//! // Option is a MonadPlus where None is mzero and mplus takes the first Some or None
//! let opt1: Option<i32> = Some(42);
//! let opt2: Option<i32> = None;
//! let opt3: Option<i32> = Some(7);
//!
//! // Using mplus directly
//! assert_eq!(Option::<i32>::mzero::<i32>(), None);
//! assert_eq!(opt1.mplus(&opt2), Some(42));
//! assert_eq!(opt2.mplus(&opt3), Some(7));
//! assert_eq!(opt2.mplus(&opt2), None);
//!
//! // MonadPlus with bind (>>=)
//! let result = opt1.bind(|x| {
//!     if *x > 40 {
//!         Option::<i32>::mzero()
//!     } else {
//!         Some(x * 2)
//!     }
//! });
//! assert_eq!(result, None);
//! ```

use std::fmt::Debug;

use crate::traits::monad::Monad;

/// A trait for monads that can represent a choice between multiple values.
///
/// MonadPlus extends the basic Monad trait with operations for alternative
/// computations, providing a "zero" element (mzero) and a way to combine
/// alternatives (mplus).
///
/// # Type Parameters
/// * None explicit, but the implementing type must be a Monad
///
/// # Laws
/// For a valid MonadPlus implementation, the following laws must hold:
///
/// 1. Identity: `mzero().mplus(&x) == x` and `x.mplus(&mzero()) == x`
///    - Zero is a neutral element for mplus
///
/// 2. Associativity: `a.mplus(&b).mplus(&c) == a.mplus(&b.mplus(&c))`
///    - The mplus operation is associative
///
/// 3. Left Zero: `mzero().bind(f) == mzero()`
///    - Zero is annihilator for bind
///
/// 4. Right Zero: `x.bind(|_| mzero()) == mzero()`
///    - Zero is annihilator for bind in the other direction
///
/// 5. Left Distribution: `a.mplus(&b).bind(f) == a.bind(f).mplus(&b.bind(f))`
///    - Bind distributes over mplus
pub trait MonadPlus: Monad {
    /// Creates a monad that represents an empty or failed computation.
    ///
    /// This is the identity element for the mplus operation.
    ///
    /// # Type Parameters
    /// * `T`: The type of value that would be contained in a successful computation
    ///
    /// # Returns
    /// A new monadic value representing failure or empty computation
    fn mzero<T: Clone>() -> Self::Output<T>;

    /// Combines two monads, representing a choice between them.
    ///
    /// In most implementations, this takes the first non-empty/non-failure value.
    ///
    /// # Parameters
    /// * `other`: Another monadic value to combine with this one
    ///
    /// # Returns
    /// A combined monadic value representing a choice between the two
    fn mplus(&self, other: &Self) -> Self;

    /// Combines two monads, consuming both.
    ///
    /// This is an owned variant of mplus that can avoid cloning in some cases.
    ///
    /// # Parameters
    /// * `other`: Another monadic value to combine with this one
    ///
    /// # Returns
    /// A combined monadic value representing a choice between the two
    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized;
}

// Implementation for Option
impl<T: Clone> MonadPlus for Option<T> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        None
    }

    fn mplus(&self, other: &Self) -> Self {
        match self {
            Some(_) => self.clone(),
            None => other.clone(),
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        match self {
            Some(_) => self,
            None => other,
        }
    }
}

// Implementation for Result with a shared error type
impl<T: Clone, E: Clone + Debug> MonadPlus for Result<T, E> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        // For Result, we need an error value to represent "zero"
        // This is a bit problematic without a Default for E
        // For a proper implementation, we might need a different trait bound
        panic!("Result cannot implement MonadPlus properly without a default error value");
    }

    fn mplus(&self, other: &Self) -> Self {
        match self {
            Ok(_) => self.clone(),
            Err(_) => other.clone(),
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        match self {
            Ok(_) => self,
            Err(_) => other,
        }
    }
}
