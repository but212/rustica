use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::fntype::{ApplyFn, SendSyncFn};
use crate::category::hkt::ReturnTypeConstraints;

/// A trait for applicative functors, which allow function application within a context.
pub trait Applicative<A>: Functor<A> + Pure<A>
where
    A: ReturnTypeConstraints,
{
    /// Apply a wrapped function to a wrapped value.
    ///
    /// # Parameters
    /// - `self`: The applicative functor instance.
    /// - `f`: A wrapped function that takes a value of type `A` and returns a value of type `B`.
    ///
    /// # Returns
    /// A new applicative functor containing the result of applying the function `f` to the wrapped value.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `B`.
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B>;

    /// Lift a binary function to actions.
    ///
    /// # Parameters
    /// - `self`: The applicative functor instance.
    /// - `b`: A wrapped value of type `B`.
    /// - `f`: A binary function that takes values of type `A` and `B` and returns a value of type `C`.
    ///
    /// # Returns
    /// A new applicative functor containing the result of applying the function `f` to the wrapped values.
    ///
    /// # Type Parameters
    /// - `B`: The type of the second wrapped value.
    /// - `C`: The return type of the function `f`.
    /// - `F`: A function type that takes values of type `A` and `B` and returns a value of type `C`.
    fn lift2<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>;

    /// Lift a ternary function to actions.
    ///
    /// # Parameters
    /// - `self`: The applicative functor instance.
    /// - `b`: A wrapped value of type `B`.
    /// - `c`: A wrapped value of type `C`.
    /// - `f`: A ternary function that takes values of type `A`, `B`, and `C` and returns a value of type `D`.
    ///
    /// # Returns
    /// A new applicative functor containing the result of applying the function `f` to the wrapped values.
    ///
    /// # Type Parameters
    /// - `B`: The type of the second wrapped value.
    /// - `C`: The type of the third wrapped value.
    /// - `D`: The return type of the function `f`.
    /// - `F`: A function type that takes values of type `A`, `B`, and `C` and returns a value of type `D`.
    fn lift3<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>;
}
