use crate::traits::hkt::HKT;

pub trait NaturalTransformation<F, G>
where
    F: HKT,
    G: HKT,
{
    fn transform<A>(&self, fa: &F::Output<A>) -> G::Output<A>
    where
        A: Clone;
}
