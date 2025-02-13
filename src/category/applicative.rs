use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::fntype::FnTrait;
use crate::category::hkt::TypeConstraints;

/// Applicative functors allow function application within a context.
///
/// # Type Parameters
/// * `A` - The type of the value within the applicative functor.
///
/// # Laws
/// 1. Identity: `pure(id).apply(v) = v`
/// 2. Composition: `pure(compose).apply(u).apply(v).apply(w) = u.apply(v.apply(w))`
/// 3. Homomorphism: `pure(f).apply(pure(x)) = pure(f(x))`
/// 4. Interchange: `u.apply(pure(y)) = pure(|f| f(y)).apply(u)`
/// 5. Naturality: `fmap(f)(x.apply(y)) = x.apply(fmap(|g| f.compose(g))(y))`
/// 6. Functor Consistency: `pure(x).fmap(f) = pure(f(x))`
///
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Clone, Eq, PartialEq, Debug, Default)]
/// struct MyApplicative<T: TypeConstraints>(T);
/// 
/// impl<T: TypeConstraints> HKT for MyApplicative<T> {
///     type Output<U> = MyApplicative<U> where U: TypeConstraints;
/// }
/// 
/// impl<T: TypeConstraints> Functor<T> for MyApplicative<T> {
///     fn fmap<U, F>(self, f: F) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         F: FnTrait<T, U>,
///     {
///         MyApplicative(f.call(self.0))
///     }
/// }
///
/// impl<T: TypeConstraints> Pure<T> for MyApplicative<T> {
///     fn pure(x: T) -> Self { MyApplicative(x) }
/// }
///
/// impl<T: TypeConstraints> Applicative<T> for MyApplicative<T> {
///     fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
///     where
///         B: TypeConstraints,
///         F: FnTrait<T, B>,
///     {
///         MyApplicative(f.0.call(self.0))
///     }
///
///     fn lift2<B, C, F>(
///         self,
///         b: Self::Output<B>,
///         f: F,
///     ) -> Self::Output<C>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         F: FnTrait<(T, B), C>,
///     {
///         MyApplicative(f.call((self.0, b.0)))
///     }
///     
///     fn lift3<B, C, D, F>(
///         self,
///         b: Self::Output<B>,
///         c: Self::Output<C>,
///         f: F,
///     ) -> Self::Output<D>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         D: TypeConstraints,
///         F: FnTrait<(T, B, C), D>,
///     {
///         MyApplicative(f.call((self.0, b.0, c.0)))
///     }
/// }
///
/// let result = MyApplicative(5).apply(MyApplicative(FnType::new(|x: i32| x + 1)));
/// assert_eq!(result.0, 6);
/// ```
pub trait Applicative<A>: Functor<A> + Pure<A>
where
    A: TypeConstraints,
{
    /// Applies a function wrapped in the applicative context to a value in the same context.
    ///
    /// # Type Parameters
    /// * `B` - The return type of the applied function
    /// * `F` - The function type to be applied
    ///
    /// # Parameters
    /// * `self` - The applicative containing the value to apply the function to
    /// * `f` - The applicative containing the function to apply
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the value
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>;
        

    /// Lifts a binary function to actions.
    ///
    /// This method takes a function that operates on two arguments and two applicative values,
    /// and returns a new applicative value containing the result of applying the function to
    /// the values inside the applicatives.
    ///
    /// # Type Parameters
    /// * `B` - The type of the second argument
    /// * `C` - The return type of the function
    /// * `F` - The type of the function to lift
    ///
    /// # Parameters
    /// * `self` - The first applicative value
    /// * `b` - The second applicative value
    /// * `f` - The function to lift
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the values
    fn lift2<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>;

    /// Lifts a ternary function to actions.
    ///
    /// This method takes a function that operates on three arguments and three applicative values,
    /// and returns a new applicative value containing the result of applying the function to
    /// the values inside the applicatives.
    ///
    /// # Type Parameters
    /// * `B` - The type of the second argument
    /// * `C` - The type of the third argument
    /// * `D` - The return type of the function
    /// * `F` - The type of the function to lift
    ///
    /// # Parameters
    /// * `self` - The first applicative value
    /// * `b` - The second applicative value
    /// * `c` - The third applicative value
    /// * `f` - The function to lift
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the values
    fn lift3<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(A, B, C), D>;
}
