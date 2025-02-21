use crate::fntype::FnTrait;
use crate::traits::hkt::{HKT, TypeConstraints};

/// A trait for bifunctors, which are functors that can map over two type parameters.
/// 
/// # Type Parameters
/// * `A` - The first type parameter
/// * `B` - The second type parameter
/// 
/// # Laws
/// 1. Identity: `bimap(id, id) = id`
/// 2. Composition: `bimap(f . g, h . i) = bimap(f, h) . bimap(g, i)`
/// 3. First Map Identity: `first(id) = id`
/// 4. Second Map Identity: `second(id) = id`
/// 5. First-Second Consistency: `bimap(f, g) = first(f) . second(g)`
pub trait Bifunctor<A, B>: HKT
where
    A: TypeConstraints,
    B: TypeConstraints,
{
    /// The type constructor for the bifunctor
    type Output<C, D>: HKT where C: TypeConstraints, D: TypeConstraints;

    /// Map over the first type parameter
    fn first<C, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<C, B>
    where
        C: TypeConstraints,
        F: FnTrait<A, C>;

    /// Map over the second type parameter
    fn second<D, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<A, D>
    where
        D: TypeConstraints,
        F: FnTrait<B, D>;

    /// Map over both type parameters
    fn bimap<C, D, F, G>(self, f: F, g: G) -> <Self as Bifunctor<A, B>>::Output<C, D>
    where
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<A, C>,
        G: FnTrait<B, D>;
}