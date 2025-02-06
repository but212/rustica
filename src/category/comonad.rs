use crate::category::functor::Functor;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{SendSyncFn, SendSyncFnTrait};

/// A comonad is the categorical dual of a monad. While a monad adds a layer of context
/// to values, a comonad extracts values from a context.
///
/// # Type Parameters
/// * `T` - The type of value contained in the comonad
///
/// # Laws
/// A comonad must satisfy these laws:
/// 1. Left Identity: `extract(duplicate(w)) = w`
/// 2. Right Identity: `duplicate(extract(w)) = w`
/// 3. Associativity: `duplicate(duplicate(w)) = map(duplicate)(duplicate(w))`
pub trait Comonad<T>: Functor<T> + ReturnTypeConstraints
where
    T: ReturnTypeConstraints,
{
    /// Extracts a value from a comonad.
    ///
    /// # Returns
    /// The extracted value of type `T`.
    fn extract(&self) -> T;

    /// Extends a comonad by duplicating the context.
    ///
    /// # Parameters
    /// - `self`: The comonad instance.
    /// - `f`: A function that takes a comonad and returns a value of type `U`.
    ///
    /// # Returns
    /// A new comonad containing the result of applying the function `f` to the comonad.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a comonad and returns a value of type `U`.
    fn extend<U, F>(self, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<Self, U>;

    /// Maps a function over a comonad.
    ///
    /// # Parameters
    /// - `self`: The comonad instance.
    /// - `f`: A function that takes a comonad and returns a value of type `U`.
    ///
    /// # Returns
    /// A new comonad containing the result of applying the function `f` to the comonad.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a comonad and returns a value of type `U`.
    fn comap<U, F>(self, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<Self, U>,
    {
        let g = SendSyncFn::new(move |w: Self| f.call(w));
        self.extend(g)
    }

    /// Duplicates the context of a comonad.
    ///
    /// # Returns
    /// A new comonad containing the duplicated context.
    fn duplicate(self) -> Self
    where
        Self: Sized,
    {
        self.extend(SendSyncFn::new(|w| w))
    }
}

/// A trait for functions that can be used with comonads.
pub trait ComonadFn<T, U, W>
where
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Parameters
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U;
}

impl<T, U, W, F> ComonadFn<T, U, W> for F
where
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
    F: Fn(&W) -> U + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Parameters
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U {
        self(w)
    }
}
