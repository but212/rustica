use crate::category::applicative::Applicative;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::FnTrait;
use crate::category::category::Category;

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
///    `m.bind(|x| pure(f(x))) = m.fmap(f)`
/// 5. Join Consistency: For any monad `m`,
///    `m.bind(f) = m.fmap(f).join()`
/// 6. Pure Preservation: For any value `x`,
///    `join(pure(pure(x))) = pure(x)`
/// 7. Natural Transformation: For any natural transformation `η`,
///    `η(m.bind(f)) = η(m).bind(η ∘ f)`
/// 8. Category Consistency: For any monad `m` and functions `f`, `g`,
///    `m.bind(f).bind(g) = m.bind(compose_morphisms(f, g))`
///
pub trait Monad<T>: Applicative<T> + Category
where
    T: ReturnTypeConstraints,
{
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
        T: Into<Self::Output<U>>;

    /// Bind operation (flatMap).
    /// 
    /// # Type Parameters
    /// * `U` - The type of the value in the resulting monad.
    /// * `F` - The type of the function to apply.
    /// 
    /// # Arguments
    /// * `f` - The function to apply.
    /// 
    /// # Returns
    /// * `Self::Output<U>` - The resulting monad.
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, Self::Output<U>>;

    /// Kleisli composition of monadic functions.
    /// 
    /// # Type Parameters
    /// * `B` - The intermediate type.
    /// * `C` - The final type.
    /// * `G` - The type of the first function.
    /// * `H` - The type of the second function.
    /// 
    /// # Arguments
    /// * `g` - The first function.
    /// * `h` - The second function.
    /// 
    /// # Returns
    /// * `Self::Morphism<T, Self::Output<C>>` - The composed function.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> Self::Morphism<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<T, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>;
}
