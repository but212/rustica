use crate::traits::functor::Functor;
use crate::traits::pure::Pure;

/// A trait for applicative functors, which allow function application within a context.
///
/// Applicative functors extend regular functors by allowing:
/// 1. Lifting of pure values into the context (via `Pure`)
/// 2. Application of functions that are themselves wrapped in the context
/// 3. Sequential application of multiple wrapped values
///
/// # Laws
///
/// For a valid Applicative implementation:
///
/// 1. Identity:
/// ```text
///    pure(id).apply(v) == v
/// ```
///
/// 2. Homomorphism:
/// ```text
///    pure(f).apply(pure(x)) == pure(f(x))
/// ```
///
/// 3. Interchange:
/// ```text
///    u.apply(pure(y)) == pure(f => f(y)).apply(u)
/// ```
///
/// 4. Composition:
/// ```text
///    pure(compose).apply(u).apply(v).apply(w) == u.apply(v.apply(w))
/// ```
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::traits::composable::Composable;
///
/// // Define a simple Option-like type
/// enum Maybe<T> {
///     Just(T),
///     Nothing,
/// }
///
/// impl<T> HKT for Maybe<T> {
///     type Source = T;
///     type Output<U> = Maybe<U>;
///     type Source2 = ();
///     type BinaryOutput<U, V> = ();
/// }
///
/// impl<T> Pure for Maybe<T> {
///     fn pure<U>(x: U) -> Self::Output<U> {
///         Maybe::Just(x)
///     }
/// }
///
/// impl<T> Functor for Maybe<T> {
///     fn fmap<B, F>(&self, f: F) -> Self::Output<B>
///     where
///         F: Fn(&Self::Source) -> B,
///     {
///         match self {
///             Maybe::Just(x) => Maybe::Just(f(x)),
///             Maybe::Nothing => Maybe::Nothing,
///         }
///     }
/// }
///
/// impl<T> Applicative for Maybe<T> {
///     fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
///     where
///         F: Fn(&Self::Source) -> B,
///     {
///         match (self, f) {
///             (Maybe::Just(x), Maybe::Just(func)) => Maybe::Just(func(x)),
///             _ => Maybe::Nothing,
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
///         Self::Source: Clone,
///         B: Clone,
///         C: Clone,
///     {
///         match (self, b) {
///             (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f(a, b)),
///             _ => Maybe::Nothing,
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
///         Self::Source: Clone,
///         B: Clone,
///         C: Clone,
///         D: Clone,
///     {
///         match (self, b, c) {
///             (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(a, b, c)),
///             _ => Maybe::Nothing,
///         }
///     }
///
///     fn sequence_right<B>(
///         &self,
///         other: &Self::Output<B>,
///     ) -> Self::Output<B>
///     where
///         Self::Source: Clone,
///         B: Clone,
///     {
///         self.lift2(other, |_: &Self::Source, b: &B| b.clone())
///     }
///
///     fn sequence_left<B>(
///         &self,
///         other: &Self::Output<B>,
///     ) -> Self::Output<Self::Source>
///     where
///         Self::Source: Clone,
///         B: Clone,
///     {
///         self.lift2(other, |a: &Self::Source, _: &B| a.clone())
///     }
///
///     // The default implementations for ap2, ap_flipped, and apply_to are usually sufficient
///     // but can be overridden for performance or specific behavior
/// }
///
/// // Using Applicative
/// let x: Maybe<i32> = Maybe::Just(5);
/// let y: Maybe<i32> = Maybe::Just(3);
/// let add = |a: &i32, b: &i32| a + b;
///
/// // Using lift2 to combine two Maybe values
/// let sum = x.lift2(&y, add);
/// match sum {
///     Maybe::Just(s) => println!("Sum: {}", s),  // Prints "Sum: 8"
///     Maybe::Nothing => println!("No sum"),
/// }
///
/// // Using ap2 for a more ergonomic interface
/// let multiply = |a: &i32, b: &i32| a * b;
/// let product = x.ap2(&y, multiply);
/// // product = Maybe::Just(15)
///
/// // Using ap_flipped to apply functions in a different order
/// let increment: Maybe<fn(&i32) -> i32> = Maybe::Just(|x| x + 1);
/// let incremented = x.ap_flipped(&increment);
/// // incremented = Maybe::Just(6)
///
/// // Applicative is useful for combining multiple independent computations
/// let validate = |name: &&str, age: &i32| {
///     format!("{} is {} years old", name, age)
/// };
///
/// let name: Maybe<&str> = Maybe::Just("Alice");
/// let age: Maybe<i32> = Maybe::Just(30);
/// let description = name.lift2(&age, validate);
/// // description = Maybe::Just("Alice is 30 years old")
///
/// // Using sequence_right and sequence_left
/// let first: Maybe<&str> = Maybe::Just("First");
/// let second: Maybe<&str> = Maybe::Just("Second");
///
/// // Keep only the second value
/// let right_result = first.sequence_right(&second);
/// // right_result = Maybe::Just("Second")
///
/// // Keep only the first value
/// let left_result = first.sequence_left(&second);
/// // left_result = Maybe::Just("First")
/// ```
pub trait Applicative: Functor + Pure {
    /// Applies a function wrapped in the applicative context to a value.
    ///
    /// This is the core operation of Applicative, allowing us to:
    /// 1. Apply a wrapped function to a wrapped value
    /// 2. Sequence operations in a context
    /// 3. Combine multiple effects
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B;

    /// Lifts a binary function to work with two applicative values.
    ///
    /// This method combines two applicative values using a binary function.
    /// It's equivalent to, but potentially more efficient than, multiple applies.
    fn lift2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C + Clone,
        Self::Source: Clone,
        B: Clone,
        C: Clone;

    /// Lifts a ternary function to work with three applicative values.
    ///
    /// This method combines three applicative values using a ternary function.
    /// It's equivalent to, but potentially more efficient than, multiple applies.
    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D + Clone,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
        D: Clone;
    
    /// Sequence a list of applicative actions, discarding the values.
    ///
    /// This method applies a list of applicative actions in sequence,
    /// keeping only the value of the final action.
    fn sequence_right<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self::Source: Clone,
        B: Clone,
    {
        self.lift2(other, |_, b| b.clone())
    }
    
    /// Sequence a list of applicative actions, discarding the final value.
    ///
    /// This method applies a list of applicative actions in sequence,
    /// keeping only the value of the first action.
    fn sequence_left<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self::Source: Clone,
        B: Clone,
    {
        self.lift2(other, |a, _| a.clone())
    }

    /// Applies an applicative function with two arguments.
    ///
    /// This is a more ergonomic alternative to nested `apply` calls.
    /// The default implementation uses `lift2`.
    fn ap2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C + Clone,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
    {
        self.lift2(b, f)
    }
    
    /// Like `apply`, but flips the order of the arguments.
    ///
    /// This can be more ergonomic in certain situations.
    /// The default implementation uses a different implementation strategy.
    fn ap_flipped<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        self.apply(f)
    }
}