use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::BindFn;
use crate::category::monad::Monad;

/// A trait for monads that support flat mapping.
pub trait FlatMap<T>: Monad<T> + Sized
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the value and flattens the result.
    ///
    /// # Parameters
    /// - `self`: The monad instance.
    /// - `f`: A function that takes a value of type `T` and returns a monad containing a value of type `U`.
    ///
    /// # Returns
    /// A new monad containing the result of applying the function `f` to the value.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `T` and returns a monad containing a value of type `U`.
    fn flat_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: BindFn<T, U, Self::Output<U>>,
    {
        self.bind(f)
    }
}
