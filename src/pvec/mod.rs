pub mod core;
pub mod error;
pub mod iter;
pub mod node;
pub mod traits;
pub mod tree;

pub use core::PersistentVector;
pub use error::PVecError;
pub use iter::{PersistentVectorIntoIter, PersistentVectorIter};

#[macro_export]
macro_rules! pvec {
    () => { PersistentVector::new() };
    ($($x:expr),+ $(,)?) => {
        PersistentVector::from_iter([$($x),+])
    };
}

pub use pvec;
