use crate::traits::hkt::TypeConstraints;
use crate::traits::traversable::Traversable;
use crate::traits::applicative::Applicative;
use crate::fntype::{FnType, FnTrait};
use crate::traits::bifunctor::Bifunctor;

/// A trait for types that can be sequenced.
/// This trait provides a way to sequence a structure of effects into an effect of structure.
/// 
/// For example:
/// - `Vec<Option<T>>` -> `Option<Vec<T>>`
/// - `Vec<Result<T, E>>` -> `Result<Vec<T>, E>`
/// 
/// # Type Parameters
/// * `A` - The type of elements in the structure
/// 
/// # Laws
/// 1. Naturality: `η(sequence(xs)) = sequence(fmap(η)(xs))`
/// 2. Identity: `sequence(fmap(pure)(xs)) = pure(xs)`
/// 3. Composition: `sequence(sequence(xss)) = sequence(fmap(sequence)(xss))`
pub trait Sequence<A>: Traversable<A>
where
    A: TypeConstraints,
{
    /// Evaluate each action in sequence from left to right, and collect the results.
    /// This is equivalent to `traverse(identity)`.
    fn sequence<F>(self) -> F::Output<<Self as Bifunctor<A, A>>::Output<A, A>>
    where
        F: Applicative<A>,
        Self: Sized,
    {
        self.traverse::<F, A, _>(FnType::new(F::pure))
    }
}

// Blanket implementation for any type that implements Traversable
impl<T: Traversable<A>, A: TypeConstraints> Sequence<A> for T {}