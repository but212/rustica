use crate::category::applicative::Applicative;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{BindFn, MonadFn, SendSyncFn};

/// A monad is a type constructor that supports sequential composition of computations.
///
/// # Laws
/// A monad must satisfy these laws:
/// 1. Left Identity: `pure(a).bind(f) = f(a)`
/// 2. Right Identity: `m.bind(pure) = m`
/// 3. Associativity: `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
/// 4. Join Laws:
///    - `join(pure(m)) = m`
///    - `join(map(pure)(m)) = m`
///    - `join(join(m)) = join(map(join)(m))`
/// 5. Kleisli Composition Laws:
///    - Identity: `kleisli_compose(pure, f) = f = kleisli_compose(f, pure)`
///    - Associativity: `kleisli_compose(kleisli_compose(f, g), h) = kleisli_compose(f, kleisli_compose(g, h))`
/// 6. Naturality: For any natural transformation η: M ~> N,
///    `η(m.bind(f)) = η(m).bind(x -> η(f(x)))`
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
