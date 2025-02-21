use crate::traits::functor::Functor;
use crate::traits::pure::Pure;
use crate::fntype::FnTrait;
use crate::traits::hkt::TypeConstraints;

/// Applicative functors allow function application within a context.
///
/// # Type Parameters
/// * `A` - The type of the value within the applicative functor.
///
/// # Laws
/// 
/// An Applicative instance must satisfy these laws:
/// 
/// 1. Identity: For any value `v`,
///    `pure(id).apply(v) = v`
/// 2. Composition: For any values `u`, `v`, `w`,
///    `pure(compose).apply(u).apply(v).apply(w) = u.apply(v.apply(w))`
/// 3. Homomorphism: For any function `f` and value `x`,
///    `pure(f).apply(pure(x)) = pure(f(x))`
/// 4. Interchange: For any applicative `u` and value `y`,
///    `u.apply(pure(y)) = pure(|f| f(y)).apply(u)`
/// 5. Naturality: For any function `f` and applicatives `x`, `y`,
///    `fmap(f)(x.apply(y)) = x.apply(fmap(|g| f.compose(g))(y))`
/// 6. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).fmap(f) = pure(f(x))`
pub trait Applicative<A>: Functor<A> + Pure<A>
where
    A: TypeConstraints,
{
    /// Applies a function wrapped in the applicative context to a value in the same context.
    ///
    /// # Type Parameters
    /// * `B` - The return type of the applied function.
    /// * `F` - The function type to be applied.
    ///
    /// # Parameters
    /// * `self` - The applicative containing the value to apply the function to.
    /// * `f` - The applicative containing the function to apply.
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the value.
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>;

    /// Lifts a binary function to actions.
    ///
    /// # Type Parameters
    /// * `B` - The type of the second argument.
    /// * `C` - The return type of the function.
    /// * `F` - The type of the function to lift.
    ///
    /// # Parameters
    /// * `self` - The first applicative value.
    /// * `b` - The second applicative value.
    /// * `f` - The function to lift.
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the values.
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
    /// # Type Parameters
    /// * `B` - The type of the second argument.
    /// * `C` - The type of the third argument.
    /// * `D` - The return type of the function.
    /// * `F` - The type of the function to lift.
    ///
    /// # Parameters
    /// * `self` - The first applicative value.
    /// * `b` - The second applicative value.
    /// * `c` - The third applicative value.
    /// * `f` - The function to lift.
    ///
    /// # Returns
    /// An applicative containing the result of applying the function to the values.
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