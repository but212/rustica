use crate::traits::functor::Functor;
use crate::traits::pure::Pure;

/// A trait for applicative functors, which allow function application within a context.
///
/// Applicative functors extend regular functors by allowing:
/// 1. Lifting of pure values into the context (via Pure)
/// 2. Application of functions that are themselves wrapped in the context
/// 3. Sequential application of multiple wrapped values
///
/// # Type Parameters
/// The trait is implemented on types that implement both `Functor` and `Pure`, where:
/// * `Source` is the type of values being transformed
/// * `Output<T>` represents the result type after transformation
///
/// # Laws
/// For a valid Applicative implementation:
///
/// 1. Identity:
/// ```text
///    pure(|x| x).apply(v) == v
/// ```
///
/// 2. Homomorphism:
/// ```text
///    pure(f).apply(pure(x)) == pure(f(x))
///```
///
/// 3. Interchange:
/// ```text
///    u.apply(pure(y)) == pure(|f| f(y)).apply(u)
///```
///
/// 4. Composition:
/// ```text
///    pure(|f| |g| |x| f(g(x))).apply(u).apply(v).apply(w) == u.apply(v.apply(w))
///```
///
/// # Examples
///
/// Basic implementation for an Option wrapper:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::functor::Functor;
/// use rustica::traits::pure::Pure;
/// use rustica::traits::applicative::Applicative;
///
/// #[derive(Clone, Debug, PartialEq, Eq)]
/// enum Option<T> {
///     Some(T),
///     None,
/// }
///
/// impl<T> HKT for Option<T> {
///     type Source = T;
///     type Output<U> = Option<U>;
/// }
///
/// impl<T> Pure for Option<T> {
///     fn pure<U>(x: U) -> Self::Output<U> {
///         Option::Some(x)
///     }
/// }
///
/// impl<T> Functor for Option<T> {
///     fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
///         match self {
///             Option::Some(x) => Option::Some(f(x)),
///             Option::None => Option::None,
///         }
///     }
/// }
///
/// impl<T> Applicative for Option<T> {
///     fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
///     where
///         F: Fn(&T) -> B,
///     {
///         match (self, f) {
///             (Option::Some(x), Option::Some(func)) => Option::Some(func(x)),
///             _ => Option::None,
///         }
///     }
///
///     fn lift2<B, C>(
///         &self,
///         b: &Self::Output<B>,
///         f: &dyn Fn(&Self::Source, &B) -> C
///     ) -> Self::Output<C> {
///         match (self, b) {
///             (Option::Some(x), Option::Some(y)) => Option::Some(f(x, y)),
///             _ => Option::None,
///         }
///     }
///
///     fn lift3<B, C, D>(
///         &self,
///         b: &Self::Output<B>,
///         c: &Self::Output<C>,
///         f: &dyn Fn(&Self::Source, &B, &C) -> D,
///     ) -> Self::Output<D> {
///         match (self, b, c) {
///             (Option::Some(x), Option::Some(y), Option::Some(z)) => Option::Some(f(x, y, z)),
///             _ => Option::None,
///         }
///     }
/// }
///
/// // Test apply
/// let x = Option::Some(5);
/// let double = Option::Some(|x: &i32| x * 2);
/// assert_eq!(x.apply(&double), Option::Some(10));
/// assert_eq!(Option::<i32>::None.apply(&double), Option::None);
/// assert_eq!(x.apply(&Option::<fn(&i32) -> i32>::None), Option::<i32>::None);
///
/// // Test lift2
/// let x = Option::Some(5);
/// let y = Option::Some(3);
/// let add = |a: &i32, b: &i32| a + b;
/// assert_eq!(x.lift2(&y, &add), Option::Some(8));
/// assert_eq!(Option::<i32>::None.lift2(&y, &add), Option::None);
/// assert_eq!(x.lift2(&Option::<i32>::None, &add), Option::None);
///
/// // Test lift3
/// let x = Option::Some(2);
/// let y = Option::Some(3);
/// let z = Option::Some(4);
/// let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
/// assert_eq!(x.lift3(&y, &z, &multiply), Option::Some(24));
/// assert_eq!(Option::<i32>::None.lift3(&y, &z, &multiply), Option::None);
/// assert_eq!(x.lift3(&Option::<i32>::None, &z, &multiply), Option::None);
/// assert_eq!(x.lift3(&y, &Option::<i32>::None, &multiply), Option::None);
///
/// // Test with different types
/// let x = Option::Some("Hello");
/// let y = Option::Some(3);
/// let repeat = |s: &&str, n: &usize| s.repeat(*n);
/// assert_eq!(x.lift2(&y, &repeat), Option::Some("HelloHelloHello".to_string()));
/// ```
/// 
/// /// # Common Use Cases
///
/// 1. **Sequencing Computations**
///    - Chaining operations that may fail or have side effects
///    - Combining multiple independent computations
///
/// 2. **Validating Input**
///    - Accumulating multiple validation errors
///    - Combining partial results into a complete object
///
/// 3. **Parsing**
///    - Building complex parsers from simpler ones
///    - Handling context-sensitive parsing
///
/// 4. **Asynchronous Operations**
///    - Managing and combining multiple asynchronous tasks
///    - Handling dependencies between asynchronous operations
pub trait Applicative: Functor + Pure {
    /// Applies a function wrapped in the applicative context to a value.
    ///
    /// This is the core operation of Applicative, allowing us to:
    /// 1. Apply a wrapped function to a wrapped value
    /// 2. Sequence operations in a context
    /// 3. Combine multiple effects
    ///
    /// # Type Parameters
    /// * `B`: The result type after applying the function
    /// * `F`: The function type that transforms Source to B
    ///
    /// # Returns
    /// The result of applying the wrapped function to the wrapped value
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B;

    /// Lifts a binary function to work with two applicative values.
    ///
    /// This is a convenience method that combines two applicative values
    /// using a binary function. It's equivalent to, but potentially more
    /// efficient than, multiple applies.
    ///
    /// # Type Parameters
    /// * `B`: The type of the second argument
    /// * `C`: The result type
    /// * `F`: The binary function type
    ///
    /// # Returns
    /// The result of applying the function to both wrapped values
    fn lift2<B, C>(&self, b: &Self::Output<B>, f: &dyn Fn(&Self::Source, &B) -> C) -> Self::Output<C>;

    /// Lifts a ternary function to work with three applicative values.
    ///
    /// This is a convenience method that combines three applicative values
    /// using a ternary function. It's equivalent to, but potentially more
    /// efficient than, multiple applies.
    ///
    /// # Type Parameters
    /// * `B`: The type of the second argument
    /// * `C`: The type of the third argument
    /// * `D`: The result type
    /// * `F`: The ternary function type
    ///
    /// # Returns
    /// The result of applying the function to all three wrapped values
    fn lift3<B, C, D>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: &dyn Fn(&Self::Source, &B, &C) -> D) -> Self::Output<D>;
}