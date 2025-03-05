//! # Rustica
//!
//! Rustica is a Rust library that provides functional programming abstractions and utilities.
//!
//! ## Structure
//!
//! The library is organized into the following main components:
//!
//! - `traits`: Fundamental traits for functional programming concepts.
//! - `datatypes`: Implementations of various functional data types.
//! - `transformers`: Monad transformers and related utilities.(unimplemented)
//! - `prelude`: A convenient module that re-exports commonly used items.
//!
//! ## Modules

/// Core traits for functional programming abstractions.
#[macro_use]
pub mod traits;

pub mod utils;

/// Implementations of functional data types.
pub mod datatypes {
    // Core data types are always included
    pub mod maybe;
    pub mod either;
    pub mod id;
    
    // Less commonly used data types are loaded only when needed
    #[cfg(feature = "advanced")]
    pub mod validated;
    
    #[cfg(feature = "advanced")]
    pub mod writer;
    
    #[cfg(feature = "advanced")]
    pub mod reader;
    
    #[cfg(feature = "advanced")]
    pub mod state;
    
    #[cfg(feature = "advanced")]
    pub mod prism;
    
    #[cfg(feature = "advanced")]
    pub mod lens;
    
    #[cfg(feature = "advanced")]
    pub mod cont;
    
    #[cfg(feature = "advanced")]
    pub mod choice;
    
    #[cfg(feature = "async")]
    pub mod async_monad;
    
    #[cfg(feature = "advanced")]
    pub mod io;
}

/// Monad transformers and related utilities.
#[cfg(feature = "transformers")]
pub mod transformers;

/// Convenient re-exports of commonly used items.
pub mod prelude {
    // Import only core traits by default
    pub use crate::traits::hkt::HKT;
    pub use crate::traits::functor::Functor;
    pub use crate::traits::applicative::Applicative;
    pub use crate::traits::monad::Monad;
    pub use crate::traits::pure::Pure;
    pub use crate::traits::identity::Identity;
    
    // Import additional traits only when needed
    #[cfg(feature = "advanced")]
    pub use crate::traits::composable::Composable;
    #[cfg(feature = "advanced")]
    pub use crate::traits::evaluate::Evaluate;
    #[cfg(feature = "advanced")]
    pub use crate::traits::category::Category;
    #[cfg(feature = "advanced")]
    pub use crate::traits::arrow::Arrow;
    #[cfg(feature = "advanced")]
    pub use crate::traits::monoid::Monoid;
    #[cfg(feature = "advanced")]
    pub use crate::traits::semigroup::Semigroup;
    #[cfg(feature = "advanced")]
    pub use crate::traits::traversable::Traversable;
    #[cfg(feature = "advanced")]
    pub use crate::traits::foldable::Foldable;
    #[cfg(feature = "advanced")]
    pub use crate::traits::comonad::Comonad;
    #[cfg(feature = "advanced")]
    pub use crate::traits::bifunctor::Bifunctor;
    #[cfg(feature = "advanced")]
    pub use crate::traits::contravariant_functor::ContravariantFunctor;
    
    // Core data types re-exports
    pub use crate::datatypes::maybe::Maybe;
    pub use crate::datatypes::either::Either;
    pub use crate::datatypes::id::Id;
    
    // Import additional data types conditionally
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::validated::Validated;
    #[cfg(feature = "async")]
    pub use crate::datatypes::async_monad::AsyncM;
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::io::IO;
}

// Additional: Utility macros for improving compile time
#[macro_export]
macro_rules! impl_functor {
    ($type:ident, $method:expr) => {
        impl<T> Functor for $type<T> {
            fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
                $method(self, f)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_pure {
    ($type:ident, $method:expr) => {
        impl<T> Pure for $type<T> {
            fn pure<U: Clone>(value: U) -> Self::Output<U> {
                $method(value)
            }
        }
    };
}