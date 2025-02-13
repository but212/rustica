use crate::prelude::*;

/// Identity monad transformer.
/// This is the simplest monad transformer that adds no additional effects.
/// It is mainly used for testing and as a base case for monad transformer stacks.
/// but it's not yet implemented.
#[derive(Clone)]
pub struct IdentityT<M, A>
where
    M: HKT + TypeConstraints,
    M::Output<A>: TypeConstraints,
    A: TypeConstraints,
{
    run: M::Output<A>,
}

