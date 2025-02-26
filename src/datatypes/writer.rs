//! # Writer Monad
//!
//! The Writer monad represents computations that produce a value along with an accumulated log or output.
//! It's a way to carry auxiliary data alongside the main computation result in a purely functional way.
//!
//! ## Core Concepts
//!
//! - **Value and Log**: Each Writer computation produces both a primary value and a log/output
//! - **Log Accumulation**: When Writer computations are chained, their logs are combined using the monoid operation
//! - **Pure Functional Logging**: Allows for logging without side effects
//!
//! ## Functional Programming Context
//!
//! In functional programming, the Writer monad solves the problem of producing output while maintaining referential
//! transparency. Instead of mutating a global log or using side effects, the Writer monad makes the output an
//! explicit part of the computation's return value.
//!
//! The Writer monad implements several functional programming abstractions:
//!
//! - **Functor**: Via the `fmap` method, allowing transformation of the value
//! - **Applicative**: Through the `combine` and `lift2` methods
//! - **Monad**: With the `bind` method for sequencing operations
//!
//! ## Use Cases
//!
//! The Writer monad is particularly useful for:
//!
//! - **Logging**: Recording information about computation steps
//! - **Collecting Metrics**: Gathering statistics during computation
//! - **Building Audit Trails**: Tracking the history of operations
//! - **Accumulating Results**: Collecting intermediate results alongside the main computation
//!
//! ## Requirements
//!
//! The log type `W` must implement the `Monoid` trait, which provides:
//!
//! - An identity element (`empty`): The starting point for accumulation
//! - A binary operation (`combine`): How to combine two logs
//!
//! ## Examples
//!
//! ### Basic Usage
//!
//! ```rust
//! use rustica::datatypes::writer::Writer;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Define a simple log type
//! #[derive(Clone, Debug, PartialEq)]
//! struct Log(Vec<String>);
//!
//! impl Semigroup for Log {
//!     fn combine(&self, other: &Self) -> Self {
//!         let mut combined = self.0.clone();
//!         combined.extend(other.0.clone());
//!         Log(combined)
//!     }
//! }
//!
//! impl Monoid for Log {
//!     fn empty() -> Self {
//!         Log(Vec::new())
//!     }
//! }
//!
//! // Create a writer that produces a value with a log entry
//! let writer = Writer::new(Log(vec!["Computed value".to_string()]), 42);
//!
//! // Extract both the value and the log
//! let (log, value) = writer.run();
//! assert_eq!(value, 42);
//! assert_eq!(log, Log(vec!["Computed value".to_string()]));
//! ```
//!
//! ### Chaining Computations
//!
//! ```rust
//! use rustica::datatypes::writer::Writer;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monad::Monad;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! struct Log(Vec<String>);
//!
//! impl Semigroup for Log {
//!     fn combine(&self, other: &Self) -> Self {
//!         let mut combined = self.0.clone();
//!         combined.extend(other.0.clone());
//!         Log(combined)
//!     }
//! }
//!
//! impl Monoid for Log {
//!     fn empty() -> Self {
//!         Log(Vec::new())
//!     }
//! }
//!
//! // Define a computation that doubles a number and logs the operation
//! let double = |x: &i32| -> Writer<Log, i32> {
//!     Writer::new(Log(vec![format!("Doubled {} to {}", x, x * 2)]), x * 2)
//! };
//!
//! // Define a computation that adds 10 to a number and logs the operation
//! let add_ten = |x: &i32| -> Writer<Log, i32> {
//!     Writer::new(Log(vec![format!("Added 10 to {} to get {}", x, x + 10)]), x + 10)
//! };
//!
//! // Chain the computations
//! let computation = Writer::new(Log(vec!["Starting with 5".to_string()]), 5);
//! let result = computation.bind(&double).bind(&add_ten);
//!
//! // Run the computation to get the final value and combined log
//! let (log, value) = result.run();
//!
//! // The value should be (5 * 2) + 10 = 20
//! assert_eq!(value, 20);
//!
//! // The log should contain entries from all three steps
//! assert_eq!(log.0.len(), 3);
//! ```

use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use crate::traits::hkt::HKT;
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::identity::Identity;
use crate::traits::composable::Composable;

/// The Writer monad represents computations that produce a value along with an accumulated log.
///
/// The Writer monad is useful for:
/// - Logging operations in a purely functional way
/// - Accumulating data alongside computations
/// - Tracking the history of operations
///
/// Type parameters:
/// - `W`: The log type, which must implement the `Monoid` trait
/// - `A`: The value type
#[derive(Clone)]
pub struct Writer<W, A> {
    /// The log produced by the computation
    log: W,
    /// The value produced by the computation
    value: A,
}

impl<W: Monoid + Clone, A> Writer<W, A> {
    /// Creates a new Writer with the given value and log.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::prelude::*;
    ///
    /// // Define a simple log type using Vec<String>
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// // Create a writer with a value and a log entry
    /// let writer: Writer<Log, i32> = Writer::new(Log(vec!["Created value 42".to_string()]), 42);
    ///
    /// // Extract the value and log
    /// let (log, value) = writer.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(log, Log(vec!["Created value 42".to_string()]));
    /// ```
    pub fn new(log: W, value: A) -> Self {
        Writer { log, value }
    }

    /// Creates a Writer with the given log and the unit value `()`.
    ///
    /// This is useful when you only care about logging something without producing a meaningful value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// // Create a writer with just a log entry and no meaningful value
    /// let writer: Writer<Log, ()> = Writer::<Log, ()>::tell(Log(vec!["Important log message".to_string()]));
    ///
    /// // Extract the value and log
    /// let (log, value) = writer.run();
    /// assert_eq!(value, ()); // Unit value
    /// assert_eq!(log, Log(vec!["Important log message".to_string()]));
    /// ```
    pub fn tell(log: W) -> Writer<W, ()> {
        Writer { log, value: () }
    }

    /// Extracts both the value and the log from the Writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// let writer = Writer::new(Log(vec!["Log entry".to_string()]), 42);
    ///
    /// // Extract both the value and the log
    /// let (log, value) = writer.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(log, Log(vec!["Log entry".to_string()]));
    /// ```
    pub fn run(self) -> (W, A) {
        (self.log, self.value)
    }

    /// Extracts just the value from the Writer, discarding the log.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::prelude::*;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// let writer = Writer::new(Log(vec!["Log entry".to_string()]), 42);
    ///
    /// // Extract just the value, discarding the log
    /// let value = writer.value();
    /// assert_eq!(value, 42);
    /// ```
    pub fn value(self) -> A {
        self.value
    }

    /// Extracts just the log from the Writer, discarding the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// let writer = Writer::new(Log(vec!["Log entry".to_string()]), 42);
    ///
    /// // Extract just the log, discarding the value
    /// let log = writer.log();
    /// assert_eq!(log, Log(vec!["Log entry".to_string()]));
    /// ```
    pub fn log(self) -> W {
        self.log
    }
}

impl<W, A> HKT for Writer<W, A> {
    /// The source type, which is the type of the value carried by the Writer.
    type Source = A;

    /// The output type, representing the Writer with a potentially different value type.
    type Output<T> = Writer<W, T>;
}

impl<W, A> Identity for Writer<W, A> {
    /// Returns a reference to the value stored in the `Writer`.
    ///
    /// This method allows access to the inner value without consuming the `Writer`.
    ///
    /// # Returns
    ///
    /// A reference to the value of type `&Self::Source`.
    fn value(&self) -> &Self::Source {
        &self.value
    }
}

impl<W: Monoid + Clone, A: Clone> Semigroup for Writer<W, A> {
    /// Combines two `Writer` instances, merging their logs and keeping the value of the first `Writer`.
    ///
    /// This implementation follows the `Semigroup` trait's `combine` operation, where:
    /// - The logs of both `Writer` instances are combined using their log type's `combine` method.
    /// - The value of the first `Writer` is retained in the result.
    ///
    /// # Arguments
    ///
    /// * `other` - Another `Writer` instance to combine with `self`.
    ///
    /// # Returns
    ///
    /// A new `Writer` instance with the combined log and the value from `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Log(Vec<String>);
    ///
    /// impl Semigroup for Log {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         combined.extend(other.0.clone());
    ///         Log(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Log {
    ///     fn empty() -> Self {
    ///         Log(Vec::new())
    ///     }
    /// }
    ///
    /// let w1 = Writer::new(Log(vec!["Log 1".to_string()]), 42);
    /// let w2 = Writer::new(Log(vec!["Log 2".to_string()]), 24);
    ///
    /// let combined = w1.combine(&w2);
    /// assert_eq!(combined.run(), (Log(vec!["Log 1".to_string(), "Log 2".to_string()]), 42));
    /// ```
    fn combine(&self, other: &Self) -> Self {
        Writer::new(self.clone().log().combine(&other.clone().log()), self.value().clone())
    }
}

impl<W: Monoid + Clone, A: Clone + Default> Monoid for Writer<W, A> {
    /// Creates an empty `Writer` instance.
    ///
    /// This method implements the `empty` operation from the `Monoid` trait.
    /// It creates a `Writer` with an empty log (using `W::empty()`) and a default value for `A`.
    ///
    /// # Returns
    ///
    /// A new `Writer` instance representing the identity element for the monoid.
    fn empty() -> Self {
        Writer::new(W::empty(), A::default())
    }
}

impl<W: Monoid + Clone, A: Clone> Functor for Writer<W, A> {
    /// Maps a function over the value inside the Writer, keeping the log unchanged.
    ///
    /// This method implements the `fmap` operation from the Functor typeclass,
    /// allowing transformation of the inner value while preserving the Writer structure.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms the inner value
    ///
    /// # Returns
    ///
    /// A new Writer with the transformed value and the original log
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::functor::Functor;
    ///
    /// let writer = Writer::new(vec!["log"], 5);
    /// let result = writer.fmap(&|x| x * 2);
    /// assert_eq!(result.run(), (vec!["log"], 10));
    /// ```
    fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
        Writer::new(self.log.clone(), f(&self.value))
    }
}

impl<W: Monoid + Clone, A: Clone> Pure for Writer<W, A> {
    fn pure<T: Clone>(value: T) -> Self::Output<T> {
        Writer::new(W::empty(), value)
    }
}

impl<W: Monoid + Clone, A: Clone> Applicative for Writer<W, A> {
    /// Applies a function wrapped in a Writer to a value in another Writer.
    ///
    /// This operation combines the logs of both Writers and applies the function to the value.
    ///
    /// # Arguments
    ///
    /// * `f` - A Writer containing a function to apply
    ///
    /// # Returns
    ///
    /// A new Writer with the combined log and the result of applying the function
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B {
        let f_value = &f.value;
        Writer::new(
            self.log.clone().combine(&f.log.clone()),
            f_value(&self.value)
        )
    }

    /// Lifts a binary function to operate on two Writers.
    ///
    /// This method combines the logs of both Writers and applies the function to their values.
    ///
    /// # Arguments
    ///
    /// * `b` - Another Writer
    /// * `f` - A function to apply to the values of both Writers
    ///
    /// # Returns
    ///
    /// A new Writer with the combined log and the result of the function application
    fn lift2<B, C>(&self, b: &Self::Output<B>, f: &dyn Fn(&Self::Source, &B) -> C) -> Self::Output<C> {
        Writer::new(
            self.log.clone().combine(&b.log.clone()),
            f(&self.value, &b.value)
        )
    }

    /// Lifts a ternary function to operate on three Writers.
    ///
    /// This method combines the logs of all three Writers and applies the function to their values.
    ///
    /// # Arguments
    ///
    /// * `b` - Second Writer
    /// * `c` - Third Writer
    /// * `f` - A function to apply to the values of all three Writers
    ///
    /// # Returns
    ///
    /// A new Writer with the combined log and the result of the function application
    fn lift3<B, C, D>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: &dyn Fn(&Self::Source, &B, &C) -> D) -> Self::Output<D> {
        Writer::new(
            self.log.clone().combine(&b.log.clone()).combine(&c.log.clone()),
            f(&self.value, &b.value, &c.value)
        )
    }
}

impl<W: Monoid + Clone, A: Clone> Monad for Writer<W, A> {
    /// Chains two Writer computations together.
    ///
    /// This method implements the `bind` operation from the Monad typeclass.
    /// It allows sequencing of Writer computations where the second computation
    /// may depend on the value produced by the first.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes the value from this Writer and returns a new Writer
    ///
    /// # Returns
    ///
    /// A new Writer with combined logs and the result of applying `f`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monad::Monad;
    ///
    /// let w1 = Writer::new(vec!["log1"], 5);
    /// let result = w1.bind(&|x| Writer::new(vec!["log2"], x * 2));
    /// assert_eq!(result.run(), (vec!["log1", "log2"], 10));
    /// ```
    fn bind<U: Clone>(&self, f: &dyn Fn(&Self::Source) -> Self::Output<U>) -> Self::Output<U> {
        let result = f(&self.value);
        Writer::new(
            self.log.clone().combine(&result.log.clone()),
            result.value.clone()
        )
    }

    /// Flattens a nested Writer structure.
    ///
    /// This method is used when you have a Writer that contains another Writer as its value.
    /// It combines the logs of both Writers and extracts the inner value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the value in the inner Writer.
    ///
    /// # Returns
    ///
    /// A new Writer with combined logs and the value from the inner Writer.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monad::Monad;
    ///
    /// let nested = Writer::new(vec!["outer"], Writer::new(vec!["inner"], 42));
    /// let flattened = nested.join();
    /// assert_eq!(flattened.run(), (vec!["outer", "inner"], 42));
    /// ```
    fn join<U>(&self) -> Self::Output<U>
        where
            Self::Source: Clone + Into<Self::Output<U>> {
        let inner: Self::Output<U> = self.value.clone().into();
        Writer::new(
            self.log.clone().combine(&inner.log),
            inner.value
        )
    }
}

impl<W: Monoid + Clone, A: Clone> Composable for Writer<W, A> {
    /// Composes two functions into a single function.
    ///
    /// This method takes two functions `f` and `g` and returns a new function that
    /// applies `f` first and then `g` to the result.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The intermediate type between `f` and `g`
    /// * `U`: The return type of the composed function
    ///
    /// # Arguments
    ///
    /// * `f`: A function that takes `Self::Source` and returns `T`
    /// * `g`: A function that takes `T` and returns `U`
    ///
    /// # Returns
    ///
    /// A new function that composes `f` and `g`
    fn compose<T, U>(f: &dyn Fn(Self::Source) -> T, g: &dyn Fn(T) -> U) -> impl Fn(Self::Source) -> U {
        move |x| g(f(x))
    }
}