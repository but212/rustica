use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::fntype::SendSyncFnTrait;

pub trait Traversable: HKT {
    fn traverse<T, U, F>(self, f: F) -> Self::Output<U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
    ;
}