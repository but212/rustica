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

pub mod pvec;

/// Implementations of functional data types.
pub mod datatypes {
    // Core data types are always included
    pub mod either;
    pub mod id;
    pub mod maybe;

    // Wrapper types for semigroups and monoids
    pub mod wrapper;

    pub mod validated;

    pub mod writer;

    pub mod reader;

    pub mod state;

    pub mod prism;

    pub mod lens;

    pub mod choice;

    #[cfg(feature = "async")]
    pub mod async_monad;

    pub mod io;

    pub mod cont;
}

/// Monad transformers and related utilities.
pub mod transformers;

/// Convenient re-exports of commonly used items.
pub mod prelude {
    // Core traits
    pub use crate::traits::alternative::Alternative;
    pub use crate::traits::applicative::Applicative;
    pub use crate::traits::composable::Composable;
    pub use crate::traits::foldable::Foldable;
    pub use crate::traits::functor::Functor;
    pub use crate::traits::hkt::HKT;
    pub use crate::traits::identity::Identity;
    pub use crate::traits::monad::Monad;
    pub use crate::traits::monoid::Monoid;
    pub use crate::traits::pure::Pure;
    pub use crate::traits::semigroup::Semigroup;

    pub use crate::transformers::MonadTransformer;

    // Convenience re-exports of commonly used datatypes
    pub use crate::datatypes::choice::Choice;
    pub use crate::datatypes::either::Either;
    pub use crate::datatypes::id::Id;
    pub use crate::datatypes::maybe::Maybe;
    pub use crate::datatypes::validated::Validated;

    pub use crate::traits::hkt::BinaryHKT;

    pub use crate::datatypes::writer::Writer;

    pub use crate::datatypes::state::State;

    pub use crate::datatypes::reader::Reader;

    // Common wrappers (feature-gated)
    pub use crate::datatypes::wrapper::first::First;

    pub use crate::datatypes::wrapper::last::Last;
}
