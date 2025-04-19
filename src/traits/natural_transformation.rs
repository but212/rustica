//! # Natural Transformation Trait
//!
//! A **natural transformation** is a morphism between two functors, preserving structure across all types.
//!
//! This trait enables generic, type-safe transformations between higher-kinded types (functors).
//!
//! ## Example
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::datatypes::either::Either;
//! use rustica::traits::natural_transformation::NaturalTransformation;
//!
//! struct MaybeToEither;
//! impl<L: Clone + Default, A: Clone> NaturalTransformation<Maybe<A>, Either<L, A>> for MaybeToEither {
//!     fn transform<T: Clone>(&self, fa: &Maybe<T>) -> Either<L, T> {
//!         match fa {
//!             Maybe::Just(a) => Either::Right(a.clone()),
//!             Maybe::Nothing => Either::Left(L::default()),
//!         }
//!     }
//! }
//! ```

use crate::traits::hkt::HKT;

/// A **natural transformation** between two functors F and G.
///
/// This trait enables generic, type-safe transformations between higher-kinded types (functors).
pub trait NaturalTransformation<F, G>
where
    F: HKT,
    G: HKT,
{
    /// Transforms a value of type `F::Output<A>` into `G::Output<A>`, preserving structure.
    ///
    /// This method converts a value from one functor context to another while maintaining the
    /// underlying structure. The transformation must satisfy the naturality condition, meaning
    /// that it commutes with functor mapping operations.
    ///
    /// # Parameters
    /// * `fa` - A reference to the source value in functor F
    ///
    /// # Returns
    /// A new value in functor G with the same underlying type
    fn transform<A>(&self, fa: &F::Output<A>) -> G::Output<A>
    where
        A: Clone,
        F::Output<A>: Clone;

    /// Transforms a value by taking ownership.
    ///
    /// This method is a convenience wrapper over `transform` that takes ownership of the input value
    /// instead of borrowing it. This can be more ergonomic in cases where you don't need the
    /// original value after transformation.
    ///
    /// # Parameters
    /// * `fa` - The source value in functor F to be consumed
    ///
    /// # Returns
    /// A new value in functor G with the same underlying type
    fn transform_owned<A>(&self, fa: F::Output<A>) -> G::Output<A>
    where
        A: Clone,
        F::Output<A>: Clone,
    {
        self.transform(&fa)
    }
}

/// Returns the identity natural transformation for any functor.
pub fn identity_nat<F: HKT>() -> impl NaturalTransformation<F, F> {
    struct Id;
    impl<F: HKT> NaturalTransformation<F, F> for Id {
        fn transform<A>(&self, fa: &F::Output<A>) -> F::Output<A>
        where
            A: Clone,
            F::Output<A>: Clone,
        {
            (*fa).clone()
        }
    }
    Id
}
