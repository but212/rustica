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
//! The key components of the monad transformer pattern:
//!
//! - **Base Monad**: The innermost monad being transformed (e.g., `Result`, `Option`, `Vec`)
//! - **Transformer**: A wrapper that adds new effects while preserving the interface
//! - **Lift**: Operations to promote values from the base monad to the transformer
//! - **Stack**: The combination of transformers and base monad creates a "stack" of effects
//!
//! ## Transformer Stacks
//!
//! Transformers are typically used in stacks, with each transformer adding a new capability:
//!
//! ```text
//! ReaderT<StateT<Option<_>>> = Environment + State + Optionality
//! ```
//!
//! In this example:
//! - `Option<_>` is the base monad, providing optional computation
//! - `StateT<_>` transforms it to add state management
//! - `ReaderT<_>` adds environment access on top
//!
//! ## Available Transformers
//!
//! This module provides the following monad transformers:
//!
//! - `ReaderT`: Adds environment capabilities
//!   - Makes an environment value available throughout a computation
//!   - Useful for dependency injection and configuration
//!
//! - `StateT`: Adds stateful computation capabilities
//!   - Allows passing and modifying state through a computation
//!   - Useful for tracking changing values without mutation
//!
//! - `WriterT`: Adds logging capabilities
//!   - Accumulates a log or other appendable data alongside computation
//!   - Useful for collecting messages, traces, or other output
//!
//! ## Implementation Pattern
//!
//! Monad transformers generally follow this implementation pattern:
//!
//! 1. Define a new type that wraps a function or value with the base monad inside
//! 2. Implement the `MonadTransformer` trait to provide lifting capabilities
//! 3. Implement the `Monad` trait to allow composition with other monads
//! 4. Provide additional methods specific to the transformer (like `run`, `exec`, etc.)
//!
//! ## Stacking Transformers
//!
//! When stacking multiple transformers, you'll need to lift values through each layer:
//!
//! ```text
//! // If you have a base monad value:
//! let base_value: Option<T> = Some(value);
//!
//! // Lift through multiple layers:
//! let value_in_state_reader_t = lift::<ReaderT<_, _, _>>(lift::<StateT<_, _, _>>(base_value));
//! ```
//!
//! ## Performance Considerations
//!
//! Monad transformers add some overhead due to their layered nature. Consider:
//!
//! - Each transformer adds a level of indirection
//! - Deep stacks may impact performance in critical sections
//! - More complex type signatures with multiple transformers
//!
//! For performance-critical code, consider using specialized combined monads
//! instead of deep transformer stacks.

use crate::traits::monad::Monad;

// mod maybe_t;
pub mod cont_t;
pub mod reader_t;
pub mod state_t;
pub mod writer_t;

// pub use maybe_t::MaybeT;
pub use reader_t::ReaderT;
pub use state_t::StateT;
pub use writer_t::WriterT;

/// Trait for monad transformers.
///
/// This trait provides a common interface for all monad transformers, allowing
/// them to be used in a generic way regardless of the specific transformer type.
/// By implementing this trait, a type declares its capability to lift values
/// from a base monad into the transformer context.
///
/// # Type Parameters
///
/// The trait requires a `BaseMonad` associated type that specifies which monad
/// is being transformed. This type must itself implement the `Monad` trait.
///
/// # Laws
///
/// Implementations must satisfy these laws:
///
/// 1. **Lift Preserves Identity:**
///    For any base monad `m` and transformer `T`:
///    ```text
///    T::lift(m.pure(x)) == T::pure(x)
///    ```
///
/// 2. **Lift Preserves Bind:**
///    For any base monad `m` and transformer `T`:
///    ```text
///    T::lift(m.bind(f)) == T::lift(m).bind(|x| T::lift(f(x)))
///    ```
///
/// # Examples
///
/// Implementing `MonadTransformer` for a state transformer:
///
/// ```rust
/// # use rustica::traits::monad::Monad;
/// # use rustica::transformers::MonadTransformer;
/// # use std::marker::PhantomData;
/// # struct StateT<S, M, A> {
/// #     run: Box<dyn Fn(&S) -> M>,
/// #     _state: PhantomData<S>,
/// #     _output: PhantomData<A>,
/// # }
/// # impl<S, M: Monad, A> StateT<S, M, A> {
/// #     fn new<F>(f: F) -> Self
/// #     where
/// #         F: Fn(&S) -> M + 'static,
/// #     {
/// #         StateT {
/// #             run: Box::new(f),
/// #             _state: PhantomData,
/// #             _output: PhantomData,
/// #         }
/// #     }
/// # }
///
/// impl<S, M, A> MonadTransformer for StateT<S, M, A>
/// where
///     M: Monad + Clone + 'static,
///     S: 'static,
///     A: 'static,
/// {
///     type BaseMonad = M;
///     
///     fn lift(base: Self::BaseMonad) -> Self {
///         StateT::new(move |_state| base.clone())
///     }
/// }
/// ```
pub trait MonadTransformer {
    /// The type of the base monad.
    ///
    /// This associated type specifies which monad is being transformed.
    /// The base monad must implement the `Monad` trait to ensure it
    /// provides the necessary operations.
    type BaseMonad: Monad;

    /// Lifts a value from the base monad into the transformer.
    ///
    /// This method takes a value from the base monad and wraps it in the
    /// transformer's context, preserving the monadic properties.
    ///
    /// # Parameters
    ///
    /// * `base` - A value in the base monad to be lifted
    ///
    /// # Returns
    ///
    /// A transformed monad containing the lifted value, preserving the
    /// semantics of the base monad while adding the transformer's capabilities.
    fn lift(base: Self::BaseMonad) -> Self;
}

/// Lifts a value from a base monad into a monad transformer.
///
/// This function provides a convenient way to lift values from a base monad
/// into a monad transformer without having to specify the transformer type
/// explicitly in the code. It uses Rust's type inference to determine the
/// correct transformer.
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
/// # use rustica::transformers::{reader_t::ReaderT, lift};
/// # use rustica::traits::monad::Monad;
/// # #[derive(Clone)]
/// # struct Env;
///
/// // Create a base monad value
/// let option_value: Option<i32> = Some(42);
///
/// // Lift it into a ReaderT transformer
/// let reader_t_value = lift::<ReaderT<Env, Option<i32>, i32>, Option<i32>>(option_value);
///
/// // Use the lifted value
/// let result = reader_t_value.run_reader(Env);
/// assert_eq!(result, Some(42));
/// ```
pub fn lift<T, M>(m: M) -> T
where
    T: MonadTransformer<BaseMonad = M>,
{
    T::lift(m)
}
