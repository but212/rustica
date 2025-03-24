use crate::traits::functor::Functor;

pub trait Distributive: Functor {
    fn distribute<G, A>(&self, ga: G::Output<Self::Source>) -> G::Output<Self>
    where
        G: Functor,
        Self::Source: Clone,
        Self: Sized;
}