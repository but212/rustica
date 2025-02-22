use std::sync::Arc;
use crate::traits::functor::Functor;
use crate::traits::hkt::AnyBox;

/// A trait for comonads, which are dual to monads.
/// 
/// # Laws
/// 
/// A Comonad instance must satisfy these laws:
/// 
/// 1. Left Identity: For any comonad `w`,
///    `w.extend(|x| x.extract()) = w`
/// 2. Right Identity: For any comonad `w` and function `f`,
///    `w.extend(f).extract() = f(w)`
/// 3. Associativity: For any comonad `w` and functions `f`, `g`,
///    `w.extend(f).extend(g) = w.extend(|x| g(x.extend(f)))`
pub trait Comonad: Functor {
    /// Extracts a value from the comonad.
    ///
    /// # Returns
    /// The extracted value wrapped in an `AnyBox`
    fn extract(&self) -> AnyBox;

    /// Duplicates the comonad structure.
    ///
    /// # Returns
    /// A nested comonad wrapped in an `AnyBox`
    fn duplicate(&self) -> AnyBox;

    /// Extends a comonadic computation.
    ///
    /// # Arguments
    /// * `f`: An `Arc`-wrapped function that takes an `AnyBox` and returns an `AnyBox`
    ///
    /// # Returns
    /// A new comonad containing the result of the computation, wrapped in an `AnyBox`
    fn extend(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;
}