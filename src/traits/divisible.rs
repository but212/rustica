use crate::traits::contravariant_functor::ContravariantFunctor;

pub trait Divisible: ContravariantFunctor {
    fn conquer<A>() -> Self::Output<A>;
    fn divide<A, B, C, F>(&self, other: &Self::Output<C>, f: F) -> Self::Output<A>
    where
        F: Fn(&A) -> (Self::Source, C),
        A: Clone;
}
