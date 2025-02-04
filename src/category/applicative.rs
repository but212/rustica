use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::fntype::{ApplyFn, SendSyncFn};
use crate::category::hkt::ReturnTypeConstraints;

/// A trait for applicative functors, which allow function application within a context.
///
/// # Example
///
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Debug, Clone, PartialEq, Default)]
/// struct Maybe<T>(Option<T>);
///
/// impl<T> Pure<T> for Maybe<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn pure(value: T) -> Self {
///         Maybe(Some(value))
///     }
/// }
/// 
/// impl<T> HKT for Maybe<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     type Output<U> = Maybe<U> where U: ReturnTypeConstraints;
/// }
/// 
/// impl<T> Functor<T> for Maybe<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn map<U, F>(self, f: F) -> Maybe<U>
///     where
///         U: ReturnTypeConstraints,
///         F: SendSyncFnTrait<T, U>,
///     {
///         match self.0 {
///             Some(x) => Maybe(Some(f.call(x))),
///             None => Maybe(None),
///         }
///     }
/// }
///
/// impl<T> Applicative<T> for Maybe<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
///     where
///         B: ReturnTypeConstraints,
///         F: ApplyFn<T, B>,
///     {
///         match (self.0, f.0) {
///             (Some(x), Some(f)) => Maybe(Some(f.call(x))),
///             _ => Maybe(None),
///         }
///     }
///
///     fn lift2<B, C, F>(
///         self,
///         b: Self::Output<B>,
///         f: F,
///     ) -> Self::Output<C>
///     where
///         B: ReturnTypeConstraints,
///         C: ReturnTypeConstraints,
///         F: ApplyFn<T, SendSyncFn<B, C>>,
///     {
///         match (self.0, b.0) {
///             (Some(a), Some(b)) => Maybe(Some(f.call(a).call(b))),
///             _ => Maybe(None),
///         }
///     }
///
///     fn lift3<B, C, D, F>(
///         self,
///         b: Self::Output<B>,
///         c: Self::Output<C>,
///         f: F,
///     ) -> Self::Output<D>
///     where
///         B: ReturnTypeConstraints,
///         C: ReturnTypeConstraints,
///         D: ReturnTypeConstraints,
///         F: ApplyFn<T, SendSyncFn<B, SendSyncFn<C, D>>>,
///     {
///         match (self.0, b.0, c.0) {
///             (Some(a), Some(b), Some(c)) => Maybe(Some(f.call(a).call(b).call(c))),
///             _ => Maybe(None),
///         }
///     }
/// }
///
/// let maybe_value = Maybe::pure(2);
/// let maybe_function = Maybe::pure(SendSyncFn::new(|x| x + 3));
/// let result = maybe_value.apply(maybe_function);
/// assert_eq!(result, Maybe::pure(5));
///
/// let maybe_value1 = Maybe::pure(2);
/// let maybe_value2 = Maybe::pure(3);
/// let maybe_function = SendSyncFn::new(|x| SendSyncFn::new(move |y| x + y));
/// let result = maybe_value1.lift2(maybe_value2, maybe_function);
/// assert_eq!(result, Maybe::pure(5));
///
/// let maybe_value1 = Maybe::pure(2);
/// let maybe_value2 = Maybe::pure(3);
/// let maybe_value3 = Maybe::pure(4);
/// let maybe_function = SendSyncFn::new(|x| SendSyncFn::new(move |y| SendSyncFn::new(move |z| x + y + z)));
/// let result = maybe_value1.lift3(maybe_value2, maybe_value3, maybe_function);
/// assert_eq!(result, Maybe::pure(9));
/// ```
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
    /// - `f`: A ternary function that takes values of type `A`, `B
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
