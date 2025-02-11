use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::fntype::{FnType, FnTrait};
use crate::category::hkt::ReturnTypeConstraints;

/// A trait for applicative functors, which allow function application within a context.
/// 
/// # Type Parameters
/// * `T` - The type of the value within the applicative functor.
/// 
/// # Laws
/// An Applicative instance must satisfy these laws:
/// 1. Identity: For any value `v`,
///    `pure(id).apply(v) = v`
/// 2. Composition: For applicatives `u`, `v`, `w`,
///    `pure(compose).apply(u).apply(v).apply(w) = u.apply(v.apply(w))`
/// 3. Homomorphism: For any function `f` and value `x`,
///    `pure(f).apply(pure(x)) = pure(f(x))`
/// 4. Interchange: For any applicative `u` and value `y`,
///    `u.apply(pure(y)) = pure(|f| f(y)).apply(u)`
/// 5. Naturality: For any function `f` and applicatives `x`, `y`,
///    `fmap(f)(x.apply(y)) = x.apply(fmap(|g| f.compose(g))(y))`
/// 6. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).fmap(f) = pure(f(x))`
///
/// # Example
///
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Debug, Clone, PartialEq, Eq, Default)]
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
///     fn fmap<U, F>(self, f: F) -> Maybe<U>
///     where
///         U: ReturnTypeConstraints,
///         F: FnTrait<T, U>,
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
///         F: FnTrait<T, B>,
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
///         F: FnTrait<T, FnType<B, C>>,
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
///         F: FnTrait<T, FnType<B, FnType<C, D>>>,
///     {
///         match (self.0, b.0, c.0) {
///             (Some(a), Some(b), Some(c)) => Maybe(Some(f.call(a).call(b).call(c))),
///             _ => Maybe(None),
///         }
///     }
/// }
///
/// let maybe_value = Maybe::pure(2);
/// let maybe_function = Maybe::pure(FnType::new(|x| x + 3));
/// let result = maybe_value.apply(maybe_function);
/// assert_eq!(result, Maybe::pure(5));
///
/// let maybe_value1 = Maybe::pure(2);
/// let maybe_value2 = Maybe::pure(3);
/// let maybe_function = FnType::new(|x| FnType::new(move |y| x + y));
/// let result = maybe_value1.lift2(maybe_value2, maybe_function);
/// assert_eq!(result, Maybe::pure(5));
///
/// let maybe_value1 = Maybe::pure(2);
/// let maybe_value2 = Maybe::pure(3);
/// let maybe_value3 = Maybe::pure(4);
/// let maybe_function = FnType::new(|x| FnType::new(move |y| FnType::new(move |z| x + y + z)));
/// let result = maybe_value1.lift3(maybe_value2, maybe_value3, maybe_function);
/// assert_eq!(result, Maybe::pure(9));
/// ```
pub trait Applicative<A>: Functor<A> + Pure<A>
where
    A: ReturnTypeConstraints,
{
    /// Apply a wrapped function to a wrapped value.
    ///
    /// # Arguments
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
        F: FnTrait<A, B>;

    /// Lift a binary function to actions.
    ///
    /// # Arguments
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
        F: FnTrait<A, FnType<B, C>>;

    /// Lift a ternary function to actions.
    ///
    /// # Arguments
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
        F: FnTrait<A, FnType<B, FnType<C, D>>>;
}
