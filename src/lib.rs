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
    pub mod either;
    pub mod id;
    pub mod maybe;

    // Wrapper types for semigroups and monoids
    pub mod wrapper;

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
    // Core traits
    pub use crate::traits::alternative::Alternative;
    pub use crate::traits::applicative::Applicative;
    pub use crate::traits::functor::Functor;
    pub use crate::traits::hkt::HKT;
    pub use crate::traits::identity::Identity;
    pub use crate::traits::monad::Monad;
    pub use crate::traits::monoid::Monoid;
    pub use crate::traits::pure::Pure;
    pub use crate::traits::semigroup::Semigroup;

    // Convenience re-exports of commonly used datatypes
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::choice::Choice;
    pub use crate::datatypes::either::Either;
    pub use crate::datatypes::id::Id;
    pub use crate::datatypes::maybe::Maybe;
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::validated::Validated;

    #[cfg(feature = "advanced")]
    pub use crate::traits::hkt::BinaryHKT;

    // Advanced datatypes (feature-gated)
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::writer::Writer;

    #[cfg(feature = "advanced")]
    pub use crate::datatypes::state::State;

    #[cfg(feature = "advanced")]
    pub use crate::datatypes::reader::Reader;

    // Common wrappers (feature-gated)
    #[cfg(feature = "advanced")]
    pub use crate::datatypes::wrapper::first::First;

    #[cfg(feature = "advanced")]
    pub use crate::datatypes::wrapper::last::Last;
}
