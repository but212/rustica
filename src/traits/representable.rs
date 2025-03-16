use crate::traits::functor::Functor;

pub trait Representable: Functor {
    type Rep;
    
    fn tabulate<F>(f: F) -> Self
    where
        F: Fn(&Self::Rep) -> Self::Source;
        
    fn index(&self, r: &Self::Rep) -> Self::Source;
}