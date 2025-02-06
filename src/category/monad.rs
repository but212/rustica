use crate::category::applicative::Applicative;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{BindFn, MonadFn, SendSyncFn};

/// A trait for monads, which are applicative functors that support sequencing of operations.
/// 
/// # Type Parameters
/// * `T` - The type of the value within the monad.
/// 
/// # Laws
/// A Monad instance must satisfy these laws:
/// 1. Left Identity: For any value `x` and function `f`,
///    `pure(x).bind(f) = f(x)`
/// 2. Right Identity: For any monad `m`,
///    `m.bind(pure) = m`
/// 3. Associativity: For any monad `m` and functions `f`, `g`,
///    `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
/// 4. Applicative Consistency: For any monad `m` and function `f`,
///    `m.bind(|x| pure(f(x))) = m.map(f)`
/// 5. Join Consistency: For any monad `m`,
///    `m.bind(f) = m.map(f).join()`
/// 6. Pure Preservation: For any value `x`,
///    `join(pure(pure(x))) = pure(x)`
/// 7. Natural Transformation: For any natural transformation `η`,
///    `η(m.bind(f)) = η(m).bind(η ∘ f)`
///
pub trait Monad<T>: Applicative<T>
where
    T: ReturnTypeConstraints,
{
    /// Bind operation.
    ///
    /// # Arguments
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
    /// # Arguments
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
    /// # Arguments
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
