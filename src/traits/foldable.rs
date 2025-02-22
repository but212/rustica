use crate::traits::hkt::{HKT, TypeOps, AnyBox};
use std::sync::Arc;

/// A trait for types that can be "folded" into a summary value.
/// 
/// This trait defines methods for reducing a structure into a single value
/// through various folding operations.
/// 
/// # Laws
/// 
/// A Foldable instance must satisfy these laws:
/// 
/// 1. Identity: For any foldable `t`,
///    `t.fold_left(|acc, x| x, init) == t.fold_right(|x, acc| x, init)`
/// 2. Composition: For any foldable `t` and functions `f`, `g`,
///    `t.fold_left(g, init).fold_left(f, init) == t.fold_left(|acc, x| f(g(acc, x), x), init)`
/// 3. Homomorphism: For any monoid `M` and foldable `t`,
///    `t.fold_map(|x| x) == t.fold_left(M::combine, M::empty())`
/// 4. Interchange: For any foldable `t` and function `f`,
///    `t.fold_right(f, init) == t.fold_left(|acc, x| f(x, acc), init)`
/// 5. Naturality: For any natural transformation `η` and foldable `t`,
///    `η(t.fold_left(f, init)) == η(t).fold_left(f, init)`
/// 6. Monoid Consistency: For any monoid `M` and foldable `t`,
///    `t.fold_left(M::combine, M::empty()) == t.fold_right(M::combine, M::empty())`
pub trait Foldable: HKT {
    /// Performs a left-associative fold of the structure.
    ///
    /// # Arguments
    ///
    /// * `init` - The initial value for the fold operation.
    /// * `f` - A function that takes the accumulator and the current element, and returns a new accumulator.
    ///
    /// # Returns
    ///
    /// The final accumulated value.
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Performs a right-associative fold of the structure.
    ///
    /// # Arguments
    ///
    /// * `init` - The initial value for the fold operation.
    /// * `f` - A function that takes the current element and the accumulator, and returns a new accumulator.
    ///
    /// # Returns
    ///
    /// The final accumulated value.
    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Maps elements to a monoid and combines them.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that maps each element to a monoid.
    ///
    /// # Returns
    ///
    /// The combined result of mapping and then combining all elements.
    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Returns the number of elements in the structure.
    ///
    /// # Returns
    ///
    /// The count of elements in the structure.
    fn length(&self) -> usize {
        if let Some(count) = self.fold_left(
            Arc::new(0usize),
            Arc::new(|acc, _| {
                if let Some(n) = acc.downcast_ref::<usize>() {
                    Arc::new(n + 1)
                } else {
                    acc
                }
            })
        ).downcast_ref::<usize>() {
            *count
        } else {
            0
        }
    }

    /// Tests if the structure is empty.
    ///
    /// # Returns
    ///
    /// `true` if the structure contains no elements, `false` otherwise.
    fn is_empty(&self) -> bool {
        self.length() == 0
    }
}

impl<T> Foldable for Vec<T>
where
    T: TypeOps + 'static
{
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut acc = init;
        for x in self {
            acc = f(acc, x.clone_box());
        }
        acc
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut acc = init;
        for x in self.iter().rev() {
            acc = f(x.clone_box(), acc);
        }
        acc
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        for x in self {
            result.push(f(x.clone_box()));
        }
        Arc::new(result)
    }
}

impl<T> Foldable for Option<T>
where
    T: TypeOps + 'static
{
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => f(init, x.clone_box()),
            None => init,
        }
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => f(x.clone_box(), init),
            None => init,
        }
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => f(x.clone_box()),
            None => Arc::new(None::<AnyBox>),
        }
    }
}

impl<T, E> Foldable for Result<T, E>
where
    T: TypeOps + 'static,
    E: TypeOps + 'static,
{
    fn fold_left(&self, init: AnyBox, _f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => x.clone_box(),
            Err(_) => init,
        }
    }

    fn fold_right(&self, init: AnyBox, _f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => x.clone_box(),
            Err(_) => init,
        }
    }

    fn fold_map(&self, _f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => x.clone_box(),
            Err(_) => Arc::new(None::<AnyBox>),
        }
    }
}