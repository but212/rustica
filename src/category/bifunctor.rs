use crate::fntype::SendSyncFnTrait;
use crate::category::hkt::ReturnTypeConstraints;

/// A bifunctor is a type constructor that is a functor in two arguments.
/// It provides a way to map over both type parameters independently or together.
///
/// # Type Parameters
/// * `A` - The first type parameter
/// * `B` - The second type parameter
///
/// # Laws
/// A bifunctor must satisfy these laws:
/// 1. Identity: `bf.bimap(|x| x, |y| y) = bf`
/// 2. Composition: `bf.bimap(f1.compose(f2), g1.compose(g2)) = bf.bimap(f1, g1).bimap(f2, g2)`
pub trait Bifunctor<A, B>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// The type constructor for the output of the bifunctor operation.
    ///
    /// # Type Parameters
    /// * `C` - The first type parameter of the output.
    /// * `D` - The second type parameter of the output.
    type Output<C, D>: Bifunctor<C, D> 
    where
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints;

    /// Maps a function over the first type parameter.
    ///
    /// # Parameters
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `A` and returns a value of type `C`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the function `f` to the first type parameter.
    ///
    /// # Type Parameters
    /// - `C`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `C`.
    fn first<C, F>(self, f: F) -> Self::Output<C, B>
    where
        C: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, C>;

    /// Maps a function over the second type parameter.
    ///
    /// # Parameters
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `B` and returns a value of type `D`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the function `f` to the second type parameter.
    ///
    /// # Type Parameters
    /// - `D`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `B` and returns a value of type `D`.
    fn second<D, F>(self, f: F) -> Self::Output<A, D>
    where
        D: ReturnTypeConstraints,
        F: SendSyncFnTrait<B, D>;

    /// Maps two functions over both type parameters simultaneously.
    ///
    /// # Parameters
    /// - `self`: The bifunctor instance.
    /// - `f`: A function that takes a value of type `A` and returns a value of type `C`.
    /// - `g`: A function that takes a value of type `B` and returns a value of type `D`.
    ///
    /// # Returns
    /// A new bifunctor containing the result of applying the functions `f` and `g` to the type parameters.
    ///
    /// # Type Parameters
    /// - `C`: The return type of the function `f`.
    /// - `D`: The return type of the function `g`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `C`.
    /// - `G`: A function type that takes a value of type `B` and returns a value of type `D`.
    fn bimap<C, D, F, G>(self, f: F, g: G) -> Self::Output<C, D>
    where
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, C>,
        G: SendSyncFnTrait<B, D>;
}
