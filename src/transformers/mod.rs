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
//! - `ReaderT`: Transformer for the `Reader` monad

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
pub fn run<T, M>(t: T) -> M
where
    T: MonadTransformer<BaseMonad = M>,
{
    t.unwrap()
}