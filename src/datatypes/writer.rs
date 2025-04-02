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
use crate::pvec::PersistentVector;
use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;

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
///
/// This implementation uses a persistent vector for efficient log accumulation,
/// leveraging structural sharing to avoid copying the entire log when combining Writer instances.
#[derive(Clone, Debug)]
pub struct Writer<W: Monoid + Clone, A> {
    /// PersistentVector that stores logs to be combined when evaluated
    logs: PersistentVector<W>,
    /// The value produced by the computation
    value: A,
}

impl<W: Monoid + Clone, A> Writer<W, A> {
    /// Create a new Writer with the given log and value.
    ///
    /// This is the basic constructor for Writer computations.
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
    /// let log = Log(vec!["Initial value computed".to_string()]);
    /// let writer = Writer::new(log, 42);
    ///
    /// let (output_log, value) = writer.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(output_log, Log(vec!["Initial value computed".to_string()]));
    /// ```
    #[inline]
    pub fn new(log: W, value: A) -> Self {
        Self {
            logs: PersistentVector::from_slice(&[log]),
            value,
        }
    }

    /// Creates a Writer with no log entries and the given value.
    ///
    /// This is useful when you want to lift a pure value into the Writer context without logging anything.
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
    /// // Create a writer with a value but no log entries
    /// let writer: Writer<Log, i32> = Writer::pure_value(42);
    ///
    /// // When run, it produces the empty log
    /// let (log, value) = writer.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(log, Log::empty());
    /// ```
    #[inline]
    pub fn pure_value(value: A) -> Self {
        Self {
            logs: PersistentVector::new(),
            value,
        }
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
    #[inline]
    pub fn tell(log: W) -> Writer<W, ()> {
        Writer::new(log, ())
    }

    /// Extracts both the value and the log from the Writer.
    /// This is where logs are combined into a single value.
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
    #[inline]
    pub fn run(self) -> (W, A) {
        // Evaluate all logs by combining them
        let mut combined_log = W::empty();

        // Iterate through the logs and combine them
        for log in self.logs.into_iter() {
            combined_log = combined_log.combine_owned(log);
        }

        (combined_log, self.value)
    }

    /// Extracts just the value from the Writer, discarding the log.
    /// This is efficient as it doesn't evaluate the logs.
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
    #[inline]
    pub fn value(self) -> A {
        self.value
    }

    /// Extracts just the log from the Writer, discarding the value.
    /// This evaluates the logs.
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
    #[inline]
    pub fn log(self) -> W {
        let (log, _) = self.run();
        log
    }
}

impl<W: Monoid + Clone, A> HKT for Writer<W, A> {
    type Source = A;
    type Output<T> = Writer<W, T>;
}

impl<W: Monoid + Clone, A> Identity for Writer<W, A> {
    #[inline]
    fn value(&self) -> &Self::Source {
        &self.value
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.value
    }

    #[inline]
    fn pure_identity<B: Clone>(value: B) -> Self::Output<B> {
        Writer::pure_value(value)
    }
}

impl<W: Monoid + Clone, A: Clone + Semigroup> Semigroup for Writer<W, A> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        // Use more efficient combination for owned values
        Self {
            logs: self.logs.concat(&other.logs),
            value: self.value.combine_owned(other.value),
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        // Use more efficient combination for references
        Self {
            logs: self.logs.concat(&other.logs),
            value: self.value.combine(&other.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone + Default + Semigroup> Monoid for Writer<W, A> {
    #[inline]
    fn empty() -> Self {
        Self {
            logs: PersistentVector::new(),
            value: A::default(),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Functor for Writer<W, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        B: Clone,
        F: Fn(&A) -> B,
    {
        Writer {
            logs: self.logs.clone(),
            value: f(&self.value),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnOnce(A) -> B,
    {
        Writer {
            logs: self.logs,
            value: f(self.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Pure for Writer<W, A> {
    #[inline]
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Writer::pure_value(value.clone())
    }
}

impl<W: Monoid + Clone, A: Clone> Applicative for Writer<W, A> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        B: Clone,
        F: Fn(&A) -> B,
    {
        Writer {
            logs: self.logs.concat(&f.logs),
            value: (f.value)(&self.value),
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: Clone,
        C: Clone,
        F: Fn(&A, &B) -> C,
    {
        Writer {
            logs: self.logs.concat(&b.logs),
            value: f(&self.value, &b.value),
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: Clone,
        C: Clone,
        D: Clone,
        F: Fn(&A, &B, &C) -> D,
    {
        Writer {
            logs: self.logs.concat(&b.logs).concat(&c.logs),
            value: f(&self.value, &b.value, &c.value),
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: Clone,
        F: FnOnce(A) -> B,
    {
        Writer {
            logs: self.logs.concat(&f.logs),
            value: (f.value)(self.value),
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: Clone,
        C: Clone,
        F: FnOnce(A, B) -> C,
    {
        Writer {
            logs: self.logs.concat(&b.logs),
            value: f(self.value, b.value),
        }
    }

    #[inline]
    fn lift3_owned<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: Clone,
        C: Clone,
        D: Clone,
        F: FnOnce(A, B, C) -> D,
    {
        Writer {
            logs: self.logs.concat(&b.logs).concat(&c.logs),
            value: f(self.value, b.value, c.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Monad for Writer<W, A> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: Fn(&A) -> Self::Output<U>,
    {
        let result = f(&self.value);
        Writer {
            logs: self.logs.concat(&result.logs),
            value: result.value,
        }
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone,
        U: Clone,
        Self::Source: Into<Self::Output<U>>,
    {
        let inner = self.value.clone().into();
        Writer {
            logs: self.logs.concat(&inner.logs),
            value: inner.value,
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: FnOnce(A) -> Self::Output<U>,
    {
        let result = f(self.value);
        Writer {
            logs: self.logs.concat(&result.logs),
            value: result.value,
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Clone,
        U: Clone,
        Self::Source: Into<Self::Output<U>>,
    {
        let inner = self.value.into();
        Writer {
            logs: self.logs.concat(&inner.logs),
            value: inner.value,
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Composable for Writer<W, A> {}

impl<W: Monoid + Clone, A: Clone> Writer<W, A> {}
