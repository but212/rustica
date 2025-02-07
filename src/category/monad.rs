use crate::category::applicative::Applicative;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{SendSyncFnTrait, SendSyncFn};

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
    /// # Type Parameters
    /// * `U` - The type of the value in the resulting monad.
    /// * `F` - The function to bind with.
    /// 
    /// # Returns
    /// * `Self::Output<U>` - The resulting monad.
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, Self::Output<U>>;

    /// Join operation.
    ///
    /// # Type Parameters
    /// * `U` - The type of the value in the resulting monad.
    /// 
    /// # Returns
    /// * `Self::Output<U>` - The resulting monad.
    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        T: Into<Self::Output<U>>,
        Self: Sized,
    {
        self.bind(SendSyncFn::new(|x: T| x.into()))
    }

    /// Kleisli composition.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first monadic function.
    /// * `H` - The type of the second monadic function.
    /// 
    /// # Returns
    /// * `SendSyncFn<A, Self::Output<C>>` - The composed function.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: SendSyncFnTrait<T, Self::Output<B>>,
        H: SendSyncFnTrait<B, Self::Output<C>>;
}
