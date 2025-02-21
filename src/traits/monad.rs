use crate::traits::applicative::Applicative;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait for monads, which are applicative functors that support sequencing of operations.
///
/// # Type Parameters
/// * `A` - The type of value contained in the monad
///
/// # Laws
/// 
/// A Monad instance must satisfy these laws:
/// 
/// 1. Left Identity: For any value `x` and function `f`,
///    `pure(x).bind(f) = f(x)`
/// 2. Right Identity: For any monad `m`,
///    `m.bind(pure) = m`
/// 3. Associativity: For any monad `m` and functions `f`, `g`,
///    `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
/// 4. Applicative Consistency: For any monad `m` and function `f`,
///    `m.bind(|x| pure(f(x))) = m.fmap(f)`
/// 5. Join Consistency: For any monad `m` and function `f`,
///    `m.bind(f) = m.fmap(f).join()`
pub trait Monad<A>: Applicative<A>
where
    A: TypeConstraints,
{
    /// Flattens a nested monad structure.
    ///
    /// # Type Parameters
    /// * `B` - The type of the inner value in the nested monad
    ///
    /// # Returns
    /// A flattened monad structure
    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>;

    /// Binds a monadic function to the monad's value.
    ///
    /// # Type Parameters
    /// * `B` - The type of the resulting monad's value
    /// * `F` - The type of the binding function
    ///
    /// # Parameters
    /// * `f` - A function that takes a value of type `A` and returns a monad of type `B`
    ///
    /// # Returns
    /// A new monad resulting from applying the binding function
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>;

    /// Sequences two monadic actions, discarding the value of the first.
    ///
    /// # Type Parameters
    /// * `B` - The type of the second monad's value
    ///
    /// # Parameters
    /// * `mb` - The second monad to sequence
    ///
    /// # Returns
    /// A monad containing the value of the second action
    fn then<B>(self, mb: Self::Output<B>) -> Self::Output<B>
    where
        B: TypeConstraints;

    /// Returns a monad containing the result of applying a function to the monad's value.
    ///
    /// # Type Parameters
    /// * `B` - The type of the resulting value
    /// * `F` - The type of the function to apply
    ///
    /// # Parameters
    /// * `f` - A function that takes a value of type `A` and returns a value of type `B`
    ///
    /// # Returns
    /// A new monad containing the result of applying the function
    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>;

    /// Maps a monadic function over the monad's value and flattens the result.
    ///
    /// This method is equivalent to `bind`, but is provided for convenience and clarity.
    ///
    /// # Type Parameters
    /// * `B` - The type of the resulting monad's value
    /// * `F` - The type of the mapping function
    ///
    /// # Parameters
    /// * `f` - A function that takes a value of type `A` and returns a monad of type `B`
    ///
    /// # Returns
    /// A new monad resulting from applying the mapping function and flattening
    fn flat_map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        self.bind(f)
    }
}