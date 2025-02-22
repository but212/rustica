use std::sync::Arc;
use crate::traits::hkt::{AnyBox, HKT};

/// A trait for contravariant functors, which are functors that map functions in the opposite direction.
///
/// Contravariant functors reverse the direction of function composition. This is useful in scenarios
/// where we want to adapt or preprocess inputs before they're used by some existing function.
///
/// # Laws
///
/// A `ContravariantFunctor` instance must satisfy the following laws:
///
/// 1. Identity: For any contravariant functor `f`,
///    `f.contramap(|x| x) == f`
///
/// 2. Composition: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(g).contramap(h) == f.contramap(|x| g(h(x)))`
///
/// These laws ensure that contravariant functors behave consistently and predictably.
pub trait ContravariantFunctor: HKT {
    /// Maps a function over the functor in the opposite direction.
    ///
    /// This method takes a function `f` and applies it to the input of the functor,
    /// effectively preprocessing the input before it's used by the functor.
    ///
    /// # Arguments
    ///
    /// * `f` - An `Arc`-wrapped function that takes an `AnyBox` and returns an `AnyBox`.
    ///         This function will be applied to the input of the functor.
    ///
    /// # Returns
    ///
    /// Returns a new `AnyBox` containing the contravariant functor with the function applied.
    fn contramap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;
}

/// Comparison functor that reverses the comparison based on a function
#[derive(Clone)]
pub struct Comparison<T>(Arc<dyn Fn(&T, &T) -> bool + Send + Sync>);

impl<T> Comparison<T> {
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&T, &T) -> bool + Send + Sync + 'static
    {
        Comparison(Arc::new(f))
    }

    pub fn compare(&self, x: &T, y: &T) -> bool {
        (self.0)(x, y)
    }
}
