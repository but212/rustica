use std::sync::Arc;
use crate::traits::hkt::{AnyBox, HKT, TypeOps};

/// A trait for semigroups, which are sets with an associative binary operation.
///
/// # Laws
///
/// A Semigroup instance must satisfy these laws:
///
/// 1. Associativity: For any values `a`, `b`, and `c`,
///    `(a.combine(b)).combine(c) = a.combine(b.combine(c))`
pub trait Semigroup: HKT {
    /// Combines two values of the same type.
    ///
    /// # Arguments
    ///
    /// * `other` - The value to combine with this one.
    ///
    /// # Returns
    ///
    /// An `AnyBox` containing the combined value.
    fn combine(&self, other: AnyBox) -> AnyBox;

    /// Combines all values in an iterator.
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator of values to combine.
    ///
    /// # Returns
    ///
    /// An `Option<AnyBox>` containing the combined value, or `None` if the iterator is empty.
    fn combine_all<I>(&self, iter: I) -> Option<AnyBox>
    where
        I: Iterator<Item = AnyBox>
    {
        iter.fold(None, |acc, x| {
            Some(match acc {
                None => x,
                Some(a) => self.combine(a)
            })
        })
    }
}

impl Semigroup for String {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_str = other.downcast_ref::<String>()
            .expect("Expected String in combine");
        Arc::new(self.clone() + other_str)
    }
}

impl<T> Semigroup for Vec<T>
where
    T: TypeOps + Clone + 'static
{
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_vec = other.downcast_ref::<Vec<T>>()
            .expect("Expected Vec in combine");
        let mut result = self.clone();
        result.extend(other_vec.iter().cloned());
        Arc::new(result)
    }
}

impl<T, E> Semigroup for Result<T, E>
where
    T: TypeOps + Clone + 'static,
    E: TypeOps + Clone + 'static
{
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_result = other.downcast_ref::<Result<T, E>>()
            .expect("Expected Result in combine");
        let result = match (self, other_result) {
            (Ok(_), Ok(other_val)) => Ok::<AnyBox, AnyBox>(other_val.clone_box()),
            (Err(_), Err(other_val)) => Err::<AnyBox, AnyBox>(other_val.clone_box()),
            _ => panic!("Incompatible types for combine")
        };
        Arc::new(result)
    }
}

impl Semigroup for i32 {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_int = other.downcast_ref::<i32>()
            .expect("Expected i32 in combine");
        Arc::new(self + other_int)
    }
}

impl Semigroup for i64 {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_int = other.downcast_ref::<i64>()
            .expect("Expected i64 in combine");
        Arc::new(self + other_int)
    }
}

impl Semigroup for f32 {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_float = other.downcast_ref::<f32>()
            .expect("Expected f32 in combine");
        Arc::new(self + other_float)
    }
}

impl Semigroup for f64 {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_float = other.downcast_ref::<f64>()
            .expect("Expected f64 in combine");
        Arc::new(self + other_float)
    }
}

impl Semigroup for bool {
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_bool = other.downcast_ref::<bool>()
            .expect("Expected bool in combine");
        Arc::new(*self && *other_bool)
    }
}

impl<T> Semigroup for Option<T>
where
    T: TypeOps + 'static
{
    fn combine(&self, other: AnyBox) -> AnyBox {
        let other_opt = other.downcast_ref::<Option<T>>()
            .expect("Expected Option in combine");
        let result = match (self, other_opt) {
            (Some(_x), Some(y)) => Some(y.clone_box()),
            (Some(x), None) => Some(x.clone_box()),
            (None, Some(y)) => Some(y.clone_box()),
            (None, None) => None,
        };
        Arc::new(result)
    }
}
