//!
//! Prelude: Monad Transformers
//!
//! This module re-exports the most important monad transformer types and traits in Rustica.
//! Monad transformers allow you to compose effects in a modular and type-safe way,
//! enabling powerful functional programming patterns in Rust.
//!
//! # Included Transformers
//!
//! - [`ContT`]: Continuation transformer for advanced control flow
//! - [`ReaderT`]: Environment transformer for dependency injection and context passing
//! - [`StateT`]: State transformer for composable stateful computations
//! - [`MonadTransformer`]: Trait for lifting monads through transformer stacks
//!
//! # Usage Example
//!
//! ```rust
//! use rustica::prelude::transformers::*;
//! use rustica::transformers::state_t::StateT;
//!
//! // StateT example: increment state and return the old value
//! let st: StateT<i32, (i32, i32), i32> = StateT::new(|s: i32| (s, s + 1));
//! let (old, new_state) = st.run_state(41);
//! assert_eq!(old, 41);
//! assert_eq!(new_state, 42);
//! ```
//!
//! See each transformer module for more advanced patterns and combinators.

pub use crate::transformers::cont_t::ContT;
pub use crate::transformers::reader_t::ReaderT;
pub use crate::transformers::state_t::StateT;
pub use crate::transformers::MonadTransformer;
