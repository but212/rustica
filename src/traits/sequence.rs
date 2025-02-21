use crate::traits::hkt::TypeConstraints;
use crate::traits::traversable::Traversable;
use crate::traits::applicative::Applicative;
use crate::fntype::{FnType, FnTrait};
use crate::traits::bifunctor::Bifunctor;

/// A trait for types that can be sequenced.
/// This trait provides a way to sequence a structure of effects into an effect of structure.
/// 
/// # Examples
/// 
/// - `Vec<Option<T>>` -> `Option<Vec<T>>`
/// - `Vec<Result<T, E>>` -> `Result<Vec<T>, E>`
/// 
/// # Type Parameters
/// 
/// * `A` - The type of elements in the structure
/// 
/// # Laws
/// 
/// A Sequence instance must satisfy these laws:
/// 
/// 1. Naturality: For any natural transformation `η: F ~> G`,
///    `η(sequence(t)) = sequence(fmap(η)(t))`
/// 2. Identity: `sequence(fmap(Identity)(t)) = Identity(t)`
/// 3. Composition: `sequence(fmap(Compose)(t)) = Compose(fmap(sequence)(sequence(t)))`
pub trait Sequence<A>: Traversable<A>
where
    A: TypeConstraints,
{
    /// Evaluates each action in the structure from left to right, and collects the results.
    /// 
    /// This method is equivalent to `traverse(identity)`.
    /// 
    /// # Type Parameters
    /// 
    /// * `F` - The applicative functor type
    /// 
    /// # Returns
    /// 
    /// An applicative functor containing the sequenced structure
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