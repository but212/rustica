use crate::traits::applicative::Applicative;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait for monads, which are applicative functors that support sequencing of operations.
///
/// # Type Parameters
/// * `A` - The type of value contained in the monad
///
/// # Laws
/// 1. Left Identity: `pure(x).bind(f) = f(x)`
/// 2. Right Identity: `m.bind(pure) = m`
/// 3. Associativity: `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
/// 4. Applicative Consistency: `m.bind(|x| pure(f(x))) = m.fmap(f)`
/// 5. Join Consistency: `m.bind(f) = m.fmap(f).join()`
pub trait Monad<A>: Applicative<A>
where
    A: TypeConstraints,
{
    /// Flattens a nested monad structure
    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>;

    /// Binds a monadic function to the monad's value
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>;

    /// Sequences two monadic actions, discarding the value of the first
    fn then<B>(self, mb: Self::Output<B>) -> Self::Output<B>
    where
        B: TypeConstraints;

    /// Returns a monad containing the result of applying a function to the monad's value
    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>;

    /// Maps a monadic function over the monad's value and flattens the result
    fn flat_map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        self.bind(f)
    }
}