use crate::category::hkt::{HKT, ReturnTypeConstraints};

pub trait Identity: HKT {
    fn identity<T>() -> Self::Output<T>
    where
        T: ReturnTypeConstraints;
}