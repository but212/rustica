//! # Monad Transformers
//! 
//! This module provides monad transformer implementations, which allow composing different
//! monadic effects into a single monad. Monad transformers solve the problem of using multiple
//! monads together without excessive nesting.
//! 
//! ## What are Monad Transformers?
//!
//! Monad transformers allow you to:
//! 
//! - Combine multiple monadic effects (like option, state, reader, etc.)
//! - Access the operations of all combined monads through a unified interface
//! - Avoid deeply nested monadic types
//! 
//! ## Core Concepts
//! 
//! The key components of monad transformers are:
//! 
//! - **Base Monad**: The innermost monad being transformed
//! - **Transformer**: A wrapper that adds new effects while preserving the interface
//! - **Lift**: Operations to promote values from the base monad to the transformer
//! 
//! ## Available Transformers
//! 
//! This module provides the following monad transformers:
//! 
//! - `OptionT`: Transformer for the `Option` monad
//! - `ReaderT`: Transformer for the `Reader` monad
//! - `StateT`: Transformer for the `State` monad
//! - `WriterT`: Transformer for the `Writer` monad
//! 
//! ## Examples
//! 
//! ```rust
//! use rustica::transformers::{OptionT, lift};
//! use rustica::prelude::*;
//! 
//! // Create an OptionT<Vec<_>> transformer
//! let values: OptionT<Vec<i32>> = OptionT::new(vec![Some(1), Some(2), None, Some(3)]);
//! 
//! // Map over the inner values
//! let doubled = values.fmap(|x| x * 2);
//! 
//! // The result combines both Option and Vec effects
//! assert_eq!(doubled.unwrap(), vec![Some(2), Some(4), None, Some(6)]);
//! 
//! // Lift a value from the base monad
//! let lifted = lift(vec![42, 43]);
//! assert_eq!(lifted.unwrap(), vec![Some(42), Some(43)]);
//! ```

use crate::traits::monad::Monad;

// mod maybe_t;
// mod state_t;
mod reader_t;
// mod writer_t;

// pub use maybe_t::MaybeT;
// pub use state_t::StateT;
pub use reader_t::ReaderT;
// pub use writer_t::WriterT;

/// Trait for monad transformers.
/// 
/// This trait provides a common interface for all monad transformers, allowing
/// them to be used in a generic way regardless of the specific transformer type.
pub trait MonadTransformer {
    /// The type of the base monad.
    type BaseMonad: Monad;
    
    /// Lifts a value from the base monad into the transformer.
    /// 
    /// # Parameters 
    /// 
    /// * `base` - A value in the base monad
    /// 
    /// # Returns
    /// 
    /// A transformed monad containing the lifted value
    fn lift(base: Self::BaseMonad) -> Self;
    
    /// Unwraps the transformer to get the underlying base monad.
    /// 
    /// # Returns
    /// 
    /// The base monad value
    fn unwrap(self) -> Self::BaseMonad;
}

/// Lifts a value from a base monad into a monad transformer.
/// 
/// This function provides a convenient way to lift values from a base monad
/// into a monad transformer.
/// 
/// # Type Parameters
/// 
/// * `T` - The monad transformer type
/// * `M` - The base monad type
/// 
/// # Parameters
/// 
/// * `m` - A value in the base monad
/// 
/// # Returns
/// 
/// A value in the transformed monad
/// 
/// # Examples
/// 
/// ```rust
/// use rustica::transformers::{OptionT, lift};
/// use rustica::prelude::*;
/// 
/// let vec_monad = vec![1, 2, 3];
/// let option_t = lift(vec_monad);
/// 
/// assert_eq!(option_t.unwrap(), vec![Some(1), Some(2), Some(3)]);
/// ```
pub fn lift<T, M>(m: M) -> T
where
    T: MonadTransformer<BaseMonad = M>,
{
    T::lift(m)
}

/// Runs a transformer monad to extract the base monad.
/// 
/// This function provides a convenient way to unwrap a transformer monad
/// and get the base monad.
/// 
/// # Type Parameters
/// 
/// * `T` - The monad transformer type
/// * `M` - The base monad type
/// 
/// # Parameters
/// 
/// * `t` - A value in the transformer monad
/// 
/// # Returns
/// 
/// The underlying value in the base monad
/// 
/// # Examples
/// 
/// ```rust
/// use rustica::transformers::{OptionT, run};
/// use rustica::prelude::*;
/// 
/// let option_t = OptionT::new(vec![Some(1), Some(2), None]);
/// let vec_monad = run(option_t);
/// 
/// assert_eq!(vec_monad, vec![Some(1), Some(2), None]);
/// ```
pub fn run<T, M>(t: T) -> M
where
    T: MonadTransformer<BaseMonad = M>,
{
    t.unwrap()
}