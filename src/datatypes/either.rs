//! # Either Datatype
//! 
//! The `Either` datatype represents values with two possibilities: a value of type `L` (Left) or a value of type `R` (Right).
//! It is a fundamental functional programming construct that is similar to Rust's built-in `Result<T, E>` but without the 
//! semantic meaning of success/failure.
//! 
//! ## Functional Programming Context
//! 
//! In functional programming, the `Either` type is commonly used for:
//! 
//! - Representing computations that can produce one of two different types of values
//! - Handling branching logic in a composable way
//! - Implementing error handling without the success/failure semantics of `Result`
//! - Building more complex data structures and control flow mechanisms
//! 
//! Similar constructs in other functional programming languages include:
//! 
//! - `Either` in Haskell
//! - `Either` in Scala
//! - `Either` in fp-ts (TypeScript)
//! - `Either` in Arrow (Kotlin)
//! 
//! ## Type Class Implementations
//! 
//! The `Either` type implements several important functional programming abstractions:
//! 
//! - `Functor`: Maps over the right value with `fmap`
//! - `Applicative`: Applies functions wrapped in `Either` to values wrapped in `Either`
//! - `Monad`: Chains computations that may produce either left or right values
//! - `Pure`: Creates an `Either` containing a right value
//! - `Identity`: Accesses the right value when present
//! - `Composable`: Composes functions that work with `Either`
//! 
//! ## Basic Usage
//! 
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::prelude::*;
//! 
//! fn example() {
//!     // Create Either values
//!     let left_value: Either<i32, &str> = Either::left(42);
//!     let right_value: Either<i32, &str> = Either::right("hello");
//!     
//!     // Pattern matching
//!     match left_value {
//!         Either::Left(n) => println!("Got left value: {}", n),
//!         Either::Right(s) => println!("Got right value: {}", s),
//!     }
//!     
//!     // Transform values using map_left and map_right
//!     let doubled = left_value.clone().map_left(|x| x * 2);  // Either::Left(84)
//!     let upper = right_value.map_right(|s| s.to_uppercase());  // Either::Right("HELLO")
//!     
//!     // Functor and Monad operations
//!     let right_val: Either<&str, i32> = Either::right(42);
//!     let mapped = right_val.clone().fmap(|x| x * 2);  // Either::Right(84)
//!     let chained = right_val.bind(|x| Either::right(x.to_string()));  // Either::Right("42")
//! }

use crate::traits::hkt::HKT;
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::traits::pure::Pure;

/// The `Either` type represents values with two possibilities: a value of type `L` or a value of type `R`.
/// This is similar to `Result<T, E>` but without the semantic meaning of success/failure.
///
/// # Type Parameters
///
/// * `L`: The type of the left value
/// * `R`: The type of the right value
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::either::Either;
/// use rustica::prelude::*;
///
/// fn example() {
///     // Create Either values
///     let left: Either<i32, &str> = Either::left(42);
///     let right: Either<i32, &str> = Either::right("hello");
///
///     // Transform values using map_left and map_right
///     let doubled = left.clone().map_left(|x| x * 2);  // Either::Left(84)
///     let upper = right.map_right(|s| s.to_uppercase());  // Either::Right("HELLO")
///
///     // Pattern matching
///     match left {
///         Either::Left(n) => println!("Got left value: {}", n),
///         Either::Right(s) => println!("Got right value: {}", s),
///     }
/// }
/// ```
///
/// # Trait Implementations
///
/// `Either` implements several important traits:
///
/// * `HKT` (Higher Kinded Type): Allows type-level programming with `Either`
/// * `Functor`: Map over the right value with `fmap`
/// * `Applicative`: Apply functions wrapped in `Either` to values in `Either`
/// * `Monad`: Chain computations that may produce either left or right values
/// * `Pure`: Create an `Either` containing a right value
/// * `Identity`: Access the right value when present
/// * `Composable`: Compose functions that work with `Either`
#[derive(Clone)]
pub enum Either<L, R> {
    /// Contains a value of type `L`
    Left(L),
    /// Contains a value of type `R`
    Right(R),
}

impl<L, R> Either<L, R> {
    /// Creates a new `Either::Left` containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// ```
    pub fn left(l: L) -> Self {
        Either::Left(l)
    }

    /// Creates a new `Either::Right` containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// ```
    pub fn right(r: R) -> Self {
        Either::Right(r)
    }

    /// Returns `true` if this is a `Left` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// assert!(left.is_left());
    /// ```
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns `true` if this is a `Right` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// assert!(right.is_right());
    /// ```
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the left value, leaving a right value unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// let doubled = left.map_left(|x| x * 2);
    /// assert_eq!(match doubled { Either::Left(n) => n, _ => 0 }, 84);
    /// ```
    pub fn map_left<T, F>(self, f: F) -> Either<T, R>
    where
        F: Fn(L) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value, leaving a left value unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// let upper = right.map_right(|s| s.to_uppercase());
    /// assert_eq!(match upper { Either::Right(s) => s, _ => String::new() }, "HELLO");
    /// ```
    pub fn map_right<T, F>(self, f: F) -> Either<L, T>
    where
        F: Fn(&R) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(&r)),
        }
    }

    /// Extracts the left value, panicking if this is a `Right`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Right` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// assert_eq!(left.unwrap_left(), 42);
    /// ```
    pub fn unwrap_left(self) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("called unwrap_left on Right value"),
        }
    }

    /// Extracts the right value, panicking if this is a `Left`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Left` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// assert_eq!(right.unwrap_right(), "hello");
    /// ```
    pub fn unwrap_right(self) -> R {
        match self {
            Either::Left(_) => panic!("called unwrap_right on Left value"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> HKT for Either<L, R> {
    type Source = R;
    type Output<T> = Either<L, T>;
    type Source2 = ();
    type BinaryOutput<T, U> = Either<T, U>;
}

impl<L, R> Pure for Either<L, R> {
    /// Creates a new `Either::Right` value containing the given value.
    ///
    /// This is the implementation of the `pure` operation for the `Pure` type class,
    /// which lifts a value into the `Either` context as a `Right` value.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The type of the value to wrap in `Either::Right`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::pure::Pure;
    ///
    /// let right: Either<&str, i32> = Either::<&str, i32>::pure(42);
    /// assert!(right.is_right());
    /// ```
    fn pure<T>(value: T) -> Self::Output<T> {
        Either::Right(value)
    }
}

impl<L: Clone, R: Clone> Functor for Either<L, R> {
    /// Maps a function over the right value, leaving a left value unchanged.
    ///
    /// This is the implementation of the `fmap` operation for the `Functor` type class.
    /// It applies the function `f` to the contained value if this is a `Right` value,
    /// otherwise it returns a new `Left` value with the same left value.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The return type of the mapping function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::functor::Functor;
    ///
    /// // Mapping over a Right value
    /// let right: Either<&str, i32> = Either::right(42);
    /// let mapped = right.fmap(|x| x * 2);
    /// assert_eq!(match mapped { Either::Right(n) => n, _ => 0 }, 84);
    ///
    /// // Mapping over a Left value (no change to the Left value)
    /// let left: Either<&str, i32> = Either::left("error");
    /// let mapped = left.fmap(|x| x * 2);
    /// assert!(mapped.is_left());
    /// ```
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }
}

impl<L: Clone, R: Clone> Applicative for Either<L, R> {
    /// Applies a function wrapped in an `Either` to a value wrapped in an `Either`.
    ///
    /// This is the implementation of the `apply` operation for the `Applicative` type class.
    /// If both `self` and `f` are `Right` values, it applies the function in `f` to the value in `self`.
    /// Otherwise, it returns the first `Left` value encountered.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The return type of the function
    /// * `F` - The function type that takes `Self::Source` and returns `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    ///
    /// // Applying a function to a value when both are Right
    /// let value: Either<&str, i32> = Either::right(42);
    /// let func: Either<&str, fn(&i32) -> i32> = Either::right(|x| x * 2);
    /// let result = value.apply(&func);
    /// assert_eq!(match result { Either::Right(n) => n, _ => 0 }, 84);
    ///
    /// // When the value is Left, the result is Left
    /// let left_value: Either<&str, i32> = Either::left("error");
    /// let func: Either<&str, fn(&i32) -> i32> = Either::right(|x| x * 2);
    /// let result = left_value.apply(&func);
    /// assert!(result.is_left());
    ///
    /// // When the function is Left, the result is Left
    /// let value: Either<&str, i32> = Either::right(42);
    /// let left_func: Either<&str, fn(&i32) -> i32> = Either::left("error");
    /// let result = value.apply(&left_func);
    /// assert!(result.is_left());
    /// ```
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f(x)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    /// Applies a binary function to values contained in two `Either` instances.
    ///
    /// This is the implementation of the `lift2` operation for the `Applicative` type class.
    /// If both `self` and `b` are `Right` values, it applies the function `f` to both values.
    /// Otherwise, it returns the first `Left` value encountered.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the value in the second `Either`
    /// * `C` - The return type of the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// // Applying a binary function to two Right values
    /// let a: Either<&str, i32> = Either::right(42);
    /// let b: Either<&str, i32> = Either::right(10);
    /// let result = a.lift2(&b, |x, y| x + y);
    /// assert_eq!(match result { Either::Right(n) => n, _ => 0 }, 52);
    ///
    /// // When one value is Left, the result is Left
    /// let a: Either<&str, i32> = Either::right(42);
    /// let b: Either<&str, i32> = Either::left("error");
    /// let result = a.lift2(&b, |x, y| x + y);
    /// assert!(result.is_left());
    /// ```
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f(x, y)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    /// Applies a ternary function to values contained in three `Either` instances.
    ///
    /// This is the implementation of the `lift3` operation for the `Applicative` type class.
    /// If `self`, `b`, and `c` are all `Right` values, it applies the function `f` to all three values.
    /// Otherwise, it returns the first `Left` value encountered.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the value in the second `Either`
    /// * `C` - The type of the value in the third `Either`
    /// * `D` - The return type of the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// // Applying a ternary function to three Right values
    /// let a: Either<&str, i32> = Either::right(42);
    /// let b: Either<&str, i32> = Either::right(10);
    /// let c: Either<&str, i32> = Either::right(5);
    /// let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    /// assert_eq!(match result { Either::Right(n) => n, _ => 0 }, 57);
    ///
    /// // When one value is Left, the result is Left
    /// let a: Either<&str, i32> = Either::right(42);
    /// let b: Either<&str, i32> = Either::right(10);
    /// let c: Either<&str, i32> = Either::left("error");
    /// let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    /// assert!(result.is_left());
    /// ```
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f(x, y, z)),
            (Either::Left(l), _, _) => Either::Left(l.clone()),
            (_, Either::Left(l), _) => Either::Left(l.clone()),
            (_, _, Either::Left(l)) => Either::Left(l.clone()),
        }
    }
}

impl<L: Clone, R: Clone> Monad for Either<L, R> {
    /// Chains this `Either` with a function that returns another `Either`.
    ///
    /// This is the implementation of the `bind` operation for the `Monad` type class.
    /// If `self` is a `Right` value, it applies the function `f` to the contained value.
    /// Otherwise, it returns a new `Left` value with the same left value.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the value in the resulting `Either`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Binding a Right value to a function
    /// let right: Either<&str, i32> = Either::right(42);
    /// let result = right.bind(|x| Either::right(x.to_string()));
    /// assert_eq!(match result { Either::Right(s) => s, _ => String::new() }, "42");
    ///
    /// // Binding a Left value (no change to the Left value)
    /// let left: Either<&str, i32> = Either::left("error");
    /// let result = left.bind(|x| Either::right(x.to_string()));
    /// assert!(result.is_left());
    ///
    /// // Chaining multiple bind operations
    /// let right: Either<&str, i32> = Either::right(42);
    /// let result = right
    ///     .bind(|x| Either::right(x * 2))
    ///     .bind(|x| Either::right(x.to_string()));
    /// assert_eq!(match result { Either::Right(s) => s, _ => String::new() }, "84");
    /// ```
    fn bind<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Self::Output<B>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => f(r),
        }
    }

    /// Flattens a nested `Either` structure.
    ///
    /// This is the implementation of the `join` operation for the `Monad` type class.
    /// If `self` is a `Right` value containing another `Either`, it returns that inner `Either`.
    /// Otherwise, it returns a new `Left` value with the same left value.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the value in the resulting `Either`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Creating a nested Either structure
    /// let nested: Either<&str, Either<&str, i32>> = Either::right(Either::right(42));
    /// 
    /// // Flattening the structure
    /// let flattened = nested.join();
    /// assert_eq!(match flattened { Either::Right(n) => n, _ => 0 }, 42);
    ///
    /// // When the outer Either is Left, the result is Left
    /// let left_outer: Either<&str, Either<&str, i32>> = Either::left("outer error");
    /// let result = left_outer.join();
    /// assert!(result.is_left());
    /// ```
    fn join<B>(&self) -> Self::Output<B>
    where
        Self::Source: Into<Self::Output<B>>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => r.clone().into(),
        }
    }
}

impl<L: Clone, R: Clone> Identity for Either<L, R> {
    /// Returns a reference to the contained value if this is a `Right` value.
    ///
    /// This is the implementation of the `value` operation for the `Identity` type class.
    /// It returns a reference to the contained value if this is a `Right` value.
    /// Otherwise, it panics.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Left` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Getting the value from a Right
    /// let right: Either<&str, i32> = Either::right(42);
    /// assert_eq!(*right.value(), 42);
    ///
    /// // Attempting to get the value from a Left would panic
    /// // let left: Either<&str, i32> = Either::left("error");
    /// // let value = left.value(); // This would panic
    /// ```
    fn value(&self) -> &Self::Source {
        match self {
            Either::Left(_) => panic!("Cannot get value from Left variant"),
            Either::Right(r) => r,
        }
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
        where
            Self::Output<A>: Identity,
            A: Clone {
            Either::Right(value.clone().into())
    }
}

impl<L, R> Composable for Either<L, R> {
    /// Composes two functions.
    ///
    /// This is the implementation of the `compose` operation for the `Composable` type class.
    /// It creates a new function that applies `f` to its argument and then applies `g` to the result.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The intermediate type between the two functions
    /// * `U` - The return type of the composed function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::composable::Composable;
    ///
    /// // Define two functions to compose
    /// let f = |x: i32| x * 2;
    /// let g = |x: i32| x.to_string();
    ///
    /// // Compose the functions
    /// let composed = Either::<(), i32>::compose(&f, &g);
    ///
    /// // Use the composed function
    /// let result = composed(21);
    /// assert_eq!(result, "42");
    /// ```
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }
}