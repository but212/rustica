use crate::traits::monad::Monad;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait for comonads, which are the categorical dual of monads.
///
/// # Type Parameters
/// * `A` - The type of value contained in the comonad
///
/// # Laws
/// 1. Left Identity: `extract(duplicate(w)) = w`
/// 2. Right Identity: `duplicate(extract(w)) = w`
/// 3. Associativity: `duplicate(duplicate(w)) = fmap(duplicate)(duplicate(w))`
/// 4. Extend/Cobind: `extend(f)(w) = fmap(f)(duplicate(w))`
/// 5. Extract Naturality: `extract(fmap(f)(w)) = f(extract(w))`
pub trait Comonad<A>: Monad<A>
where
    A: TypeConstraints,
{
    /// Extracts the value from the comonad
    fn extract(self) -> A;

    /// Creates a nested comonad structure
    fn duplicate(self) -> Self::Output<Self>
    where
        Self: Sized;

    /// Maps a function over the comonad context
    fn extend<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<Self, B>,
        Self: Sized;

    /// Extracts a value using a function
    fn extract_with<B, F>(self, f: F) -> B
    where
        B: TypeConstraints,
        F: FnTrait<Self, B>,
        Self: Sized;
}

/// A trait for functions that can be used with comonads.
pub trait ComonadFn<T, U, W>
where
    T: TypeConstraints,
    U: TypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Arguments
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U;
}

impl<T, U, W, F> ComonadFn<T, U, W> for F
where
    T: TypeConstraints,
    U: TypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
    F: Fn(&W) -> U + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Arguments
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U {
        self(w)
    }
}