use crate::prelude::*;

pub trait Traversable: HKT {
    fn traverse<T, U, F>(self, f: F) -> Self::Output<U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
    ;
}