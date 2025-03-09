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
//! 
//!     fn combine_owned(self, other: Self) -> Self {
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
//! 
//!     fn combine_owned(self, other: Self) -> Self {
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
    /// 
    ///     fn combine_owned(self, other: Self) -> Self {
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
    /// 
    ///     fn combine_owned(self, other: Self) -> Self {
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
    /// 
    ///     fn combine_owned(self, other: Self) -> Self {
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
    /// 
    ///     fn combine_owned(self, other: Self) -> Self {
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
    /// 
    ///     fn combine_owned(self, other: Self) -> Self {
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
    type Source = A;

    type Output<T> = Writer<W, T>;
}

impl<W: Monoid + Clone, A> Identity for Writer<W, A> {
    fn value(&self) -> &Self::Source {
        &self.value
    }

    fn pure_identity<B>(value: B) -> Self::Output<B>
        where
            Self::Output<B>: Identity,
            {
        Writer::new(W::empty(), value)
    }

    fn into_value(self) -> Self::Source {
        self.value
    }
}

impl<W: Monoid + Clone, A: Clone> Semigroup for Writer<W, A> {
    fn combine_owned(self, other: Self) -> Self {
        Writer::new(self.clone().log().combine_owned(other.log()), self.value().clone())
    }

    fn combine(&self, other: &Self) -> Self {
        Writer::new(self.clone().log().combine(&other.clone().log()), self.value().clone())
    }
}

impl<W: Monoid + Clone, A: Clone + Default> Monoid for Writer<W, A> {
    fn empty() -> Self {
        Writer::new(W::empty(), A::default())
    }
}

impl<W: Monoid + Clone, A: Clone> Functor for Writer<W, A> {
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B,
        {
        Writer {
            log: self.log.clone(),
            value: f(&self.value),
        }
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
        where
            F: Fn(Self::Source) -> B,
        {
        Writer {
            log: self.log,
            value: f(self.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Pure for Writer<W, A> {
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Writer::new(W::empty(), value.clone())
    }
}

impl<W: Monoid + Clone, A: Clone> Applicative for Writer<W, A> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B {
        Writer::new(
            self.log.combine(&f.log),
            (f.value)(&self.value)
        )
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        B: Clone,
    {
        Writer::new(
            self.log.combine(&b.log),
            f(&self.value, &b.value)
        )
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        B: Clone,
        C: Clone,
    {
        Writer::new(
            self.log.combine(&b.log).combine(&c.log),
            f(&self.value, &b.value, &c.value)
        )
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(Self::Source) -> B,
            Self: Sized {
        Writer::new(
            self.log.combine_owned(f.log),
            (f.value)(self.value)
        )
    }

    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: Fn(Self::Source, B) -> C,
            Self: Sized,
            B: Clone {
        Writer::new(
            self.log.combine_owned(b.log),
            f(self.value, b.value)
        )
    }

    fn lift3_owned<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
        where
            F: Fn(Self::Source, B, C) -> D,
            Self: Sized,
            B: Clone,
            C: Clone {
        Writer::new(
            self.log.combine_owned(b.log).combine_owned(c.log),
            f(self.value, b.value, c.value)
        )
    }
}

impl<W: Monoid + Clone, A: Clone> Monad for Writer<W, A> {
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        let result = f(&self.value);
        Writer::new(
            self.log.combine(&result.log),
            result.value
        )
    }

    fn join<U>(&self) -> Self::Output<U>
        where
            Self::Source: Clone + Into<Self::Output<U>> {
        let inner: Self::Output<U> = self.value.clone().into();
        Writer::new(
            self.log.combine(&inner.log),
            inner.value
        )
    }

    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
        where
            F: Fn(Self::Source) -> Self::Output<U>,
            U: Clone,
            Self: Sized {
        let result = f(self.value);
        Writer::new(
            self.log.combine_owned(result.log),
            result.value
        )
    }

    fn join_owned<U>(self) -> Self::Output<U>
        where
            Self::Source: Into<Self::Output<U>>,
            U: Clone,
            Self: Sized {
        let inner: Self::Output<U> = self.value.into();
        Writer::new(
            self.log.combine_owned(inner.log),
            inner.value
        )
    }
}

impl<W: Monoid + Clone, A: Clone> Composable for Writer<W, A> {
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }
}