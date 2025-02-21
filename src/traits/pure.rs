use crate::traits::hkt::{HKT, TypeConstraints};

/// The Pure trait represents a type that can lift a value into a context.
/// 
/// This trait is a fundamental part of the Applicative Functor abstraction,
/// allowing for the creation of a minimal context around a value.
/// 
/// # Type Parameters
/// 
/// * `T` - The type of the value to be lifted.
///
/// # Laws
/// 
/// An implementation of Pure must satisfy the following laws:
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
pub trait Pure<T>: HKT
where
    T: TypeConstraints,
{
    /// Lifts a value into the context.
    ///
    /// This method takes a value of type `T` and lifts it into the minimal context
    /// represented by the implementing type.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be lifted into the context.
    ///
    /// # Returns
    ///
    /// A new instance of the context containing the lifted value.
    ///
    /// # Example
    ///
    /// ```
    /// use rustica::traits::hkt::{HKT, TypeConstraints};
    /// use rustica::traits::pure::Pure;
    ///
    /// #[derive(Clone, PartialEq, Eq, Default)]
    /// struct MyContext<T: TypeConstraints>(T);
    /// 
    /// impl<T: TypeConstraints> HKT for MyContext<T> {
    ///     type Output<U> = MyContext<U> where U: TypeConstraints;
    /// }
    ///
    /// impl<T: TypeConstraints> Pure<T> for MyContext<T> {
    ///     fn pure(value: T) -> Self::Output<T> {
    ///         MyContext(value)
    ///     }
    /// }
    ///
    /// let lifted = MyContext::pure(42);
    /// assert_eq!(lifted.0, 42);
    /// ```
    fn pure(value: T) -> Self::Output<T>;
}