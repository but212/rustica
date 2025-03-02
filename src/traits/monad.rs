use crate::traits::applicative::Applicative;

/// A trait for monads, which are applicative functors that support sequencing of operations.
/// 
/// Monads provide a way to chain computations while maintaining context. They are particularly
/// useful for handling effects like optional values, error handling, or state management.
///
/// # Type Parameters
/// The trait inherits type parameters from `Applicative`:
/// * `Source`: The type of values being transformed
/// * `Output<T>`: The result type after transformation
///
/// # Laws
/// For a valid Monad implementation, the following laws must hold:
///
/// 1. Left Identity: 
///    pure(x).bind(f) == f(x)
///    Applying a function to a pure value should be the same as applying the function directly.
///
/// 2. Right Identity:
///    m.bind(pure) == m
///    Lifting a monadic value into a pure context should not change the value.
///
/// 3. Associativity:
///    m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
///    The order of binding operations should not matter.
///
/// 4. Applicative Consistency:
///    m.bind(|x| pure(f(x))) == m.fmap(f)
///    Binding with a pure function should be equivalent to fmap.
///
/// 5. Join Consistency:
///    m.bind(f) == m.fmap(f).join()
///    Binding can be decomposed into fmap followed by join.
///
/// # Examples
///
/// Basic implementation for Result:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::Pure;
/// use rustica::traits::functor::Functor;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::monad::Monad;
/// use rustica::traits::composable::Composable;
/// use rustica::prelude::Identity;
///
/// // A wrapper around Result to implement our traits
/// #[derive(Clone)]
/// struct MyResult<T, E>(Result<T, E>);
///
/// impl<T, E> HKT for MyResult<T, E> {
///     type Source = T;
///     type Output<U> = MyResult<U, E>;
///     type Source2 = E;
///     type BinaryOutput<U, V> = MyResult<U, V>;
/// }
///
/// impl<T, E> Pure for MyResult<T, E> {
///     fn pure<U>(x: U) -> Self::Output<U> {
///         MyResult(Ok(x))
///     }
/// }
/// 
/// impl<T, E: std::fmt::Debug> Identity for MyResult<T, E> {
///     fn value(&self) -> &Self::Source {
///         self.0.as_ref().expect("Expected Ok value, got Err")
///     }
///
///     fn pure_identity<A>(x: A) -> <Self as HKT>::Output<A>
///     where
///         A: Clone,
///         <Self as HKT>::Output<A>: Identity,
///     {
///         MyResult(Ok(x))
///     }
/// }
///
/// impl<T, E: Clone> Functor for MyResult<T, E> {
///     fn fmap<B, F>(&self, f: F) -> Self::Output<B>
///     where
///         F: Fn(&Self::Source) -> B,
///     {
///         MyResult(self.0.as_ref().map(f).map_err(Clone::clone))
///     }
/// }
/// 
/// impl<T: Clone, E: Clone> Applicative for MyResult<T, E> {
///     fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
///     where
///         F: Fn(&Self::Source) -> B,
///     {
///         match (&self.0, &f.0) {
///             (Ok(x), Ok(f)) => MyResult(Ok(f(&x))),
///             (Err(e), _) => MyResult(Err(e.clone())),
///             (_, Err(e)) => MyResult(Err(e.clone())),
///         }
///     }
///
///     fn lift2<B, C, F>(
///         &self,
///         b: &Self::Output<B>,
///         f: F,
///     ) -> Self::Output<C>
///     where
///         F: Fn(&Self::Source, &B) -> C,
///     {
///         match (&self.0, &b.0) {
///             (Ok(x), Ok(y)) => MyResult(Ok(f(&x, &y))),
///             (Err(e), _) => MyResult(Err(e.clone())),
///             (_, Err(e)) => MyResult(Err(e.clone())),
///         }
///     }
///
///     fn lift3<B, C, D, F>(
///         &self,
///         b: &Self::Output<B>,
///         c: &Self::Output<C>,
///         f: F,
///     ) -> Self::Output<D>
///     where
///         F: Fn(&Self::Source, &B, &C) -> D,
///     {
///         match (&self.0, &b.0, &c.0) {
///             (Ok(x), Ok(y), Ok(z)) => MyResult(Ok(f(&x, &y, &z))),
///             (Err(e), _, _) => MyResult(Err(e.clone())),
///             (_, Err(e), _) => MyResult(Err(e.clone())),
///             (_, _, Err(e)) => MyResult(Err(e.clone())),
///         }
///     }
/// }
///
/// impl<T: Clone, E: Clone> Monad for MyResult<T, E> {
///     fn join<U>(&self) -> Self::Output<U>
///     where
///         Self::Source: Into<Self::Output<U>>
///     {
///         match &self.0 {
///             Ok(x) => x.clone().into(),
///             Err(e) => MyResult(Err(e.clone())),
///         }
///     }
///
///     fn bind<U, F>(&self, f: F) -> Self::Output<U>
///     where
///         F: Fn(&Self::Source) -> Self::Output<U>,
///     {
///         match &self.0 {
///             Ok(x) => f(x),
///             Err(e) => MyResult(Err(e.clone())),
///         }
///     }
/// }
/// 
/// // Basic error handling
/// let success: MyResult<i32, &str> = MyResult(Ok(5));
/// let error: MyResult<i32, &str> = MyResult(Err("error"));
///
/// // Using bind for sequential operations
/// let result1 = success.bind(|x| MyResult(Ok(x + 1)));
/// assert_eq!(result1.0, Ok(6));
///
/// // Error propagation
/// let result2 = error.bind(|x| MyResult(Ok(x + 1)));
/// assert_eq!(result2.0, Err("error"));
///
/// // Chaining multiple operations
/// let result3 = success
///     .bind(|x| MyResult(Ok(x + 1)))
///     .bind(|x| MyResult(Ok(x * 2)));
/// assert_eq!(result3.0, Ok(12));
///
/// // Using join to flatten nested monads
/// let nested: MyResult<MyResult<i32, &str>, &str> = MyResult(Ok(MyResult(Ok(5))));
/// let flattened = nested.join();
/// assert_eq!(flattened.0, Ok(5));
///
/// let nested_err: MyResult<MyResult<i32, &str>, &str> = MyResult(Ok(MyResult(Err("inner error"))));
/// let flattened_err = nested_err.join();
/// assert_eq!(flattened_err.0, Err("inner error"));
/// ```
pub trait Monad: Applicative {
    /// Flattens a nested monad structure.
    ///
    /// This operation is also known as "flatten" in some contexts.
    /// It takes a monad of a monad and collapses it into a single layer.
    ///
    /// # Type Parameters
    /// * `U`: The type contained in the inner monad
    ///
    /// # Returns
    /// A monad containing the inner value directly
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>;

    /// Applies a function that returns a monadic value to the contents of this monad.
    ///
    /// This is the core operation of a monad, allowing for sequencing of monadic computations.
    /// It is also known as "flatMap" or "chain" in some contexts.
    ///
    /// # Type Parameters
    /// * `U`: The type of the resulting monadic value
    ///
    /// # Parameters
    /// * `f`: A function that takes a value of type `T` and returns a monadic value
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>;

    /// Alias for `bind` that matches common functional programming terminology.
    ///
    /// This method provides compatibility with other functional programming libraries
    /// and languages that use the term "flatMap".
    ///
    /// * `U`: The type of the resulting monadic value
    /// * `F`: The type of the function to apply
    ///
    /// # Parameters
    /// * `f`: A function that takes a value of type `T` and returns a monadic value
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    fn flat_map<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>
    {
        self.bind(f)
    }
}
