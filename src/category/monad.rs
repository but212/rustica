use crate::category::applicative::Applicative;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{BindFn, MonadFn, SendSyncFn};

/// A monad is a type constructor that supports sequential composition of computations.
///
/// A monad must satisfy the following laws:
/// 1. Left Identity: `pure(a).bind(f) = f(a)`
/// 2. Right Identity: `m.bind(pure) = m`
/// 3. Associativity: `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
pub trait Monad<T>: Applicative<T>
where
    T: ReturnTypeConstraints,
{
    /// Bind operation.
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
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: BindFn<T, U, Self::Output<U>>;

    /// Join operation.
    ///
    /// # Parameters
    /// - `self`: The monad instance.
    ///
    /// # Returns
    /// A new monad containing the result of flattening the nested monad.
    ///
    /// # Type Parameters
    /// - `U`: The type of the inner monad.
    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        T: Into<Self::Output<U>> + Send + Sync;

    /// Kleisli composition.
    ///
    /// # Parameters
    /// - `g`: A function that takes a value of type `T` and returns a monad containing a value of type `B`.
    /// - `h`: A function that takes a value of type `B` and returns a monad containing a value of type `C`.
    ///
    /// # Returns
    /// A new function that takes a value of type `T` and returns a monad containing a value of type `C`.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `g`.
    /// - `C`: The return type of the function `h`.
    /// - `G`: A function type that takes a value of type `T` and returns a monad containing a value of type `B`.
    /// - `H`: A function type that takes a value of type `B` and returns a monad containing a value of type `C`.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<T, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>;
}
