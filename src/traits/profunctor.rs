use crate::traits::hkt::BinaryHKT;

pub trait Profunctor: BinaryHKT {
    fn dimap<A, B, C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<A, D>
    where
        F: Fn(&A) -> Self::Source,
        G: Fn(&Self::Source2) -> D,
        A: Clone,
        D: Clone;
}
