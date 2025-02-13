/// This module provides a prelude for the rustica library, re-exporting commonly used traits and types.
///
/// By importing this prelude, users can easily access core functional programming abstractions
/// without having to import each trait or type individually.
///
/// # Example
///
/// ```
/// use rustica::prelude::*;
///
/// // Now you can use HKT, Functor, Monad, etc. without additional imports
/// ```
pub use crate::traits::hkt::{HKT, TypeConstraints};
pub use crate::traits::functor::Functor;
pub use crate::traits::applicative::Applicative;
pub use crate::traits::category::Category;
pub use crate::traits::arrow::Arrow;
pub use crate::traits::monad::Monad;
pub use crate::traits::pure::Pure;
pub use crate::traits::composable::Composable;
pub use crate::traits::evaluate::Evaluate;
pub use crate::traits::identity::Identity;
pub use crate::traits::monoid::Monoid;
pub use crate::traits::semigroup::Semigroup;
pub use crate::traits::traversable::Traversable;
pub use crate::traits::sequence::Sequence;
pub use crate::traits::foldable::Foldable;
pub use crate::traits::comonad::Comonad;
pub use crate::traits::bifunctor::Bifunctor;
pub use crate::traits::contravariant_functor::ContravariantFunctor;

pub use crate::fntype::{FnType, FnTrait};