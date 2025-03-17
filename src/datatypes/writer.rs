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
use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
use std::sync::Arc;

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
/// This implementation uses lazy evaluation for log combinations - logs are only combined
/// when explicitly requested, which improves performance for chains of operations.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct Writer<W, A> {
    /// Thunk that produces the log when evaluated
    log_thunk: LogThunk<W>,
    /// The value produced by the computation
    value: A,
}

/// A type to lazily evaluate and combine logs
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
enum LogThunk<W> {
    /// A simple log value
    Value(W),
    /// A thunk that will combine two logs when evaluated
    Combine(Arc<LogThunk<W>>, Arc<LogThunk<W>>),
}

impl<W: Clone> LogThunk<W> {
    /// Evaluates the thunk to produce the final log
    #[inline]
    fn evaluate(&self) -> W
    where
        W: Semigroup,
    {
        match self {
            LogThunk::Value(w) => w.clone(),
            LogThunk::Combine(left, right) => {
                let l = left.evaluate();
                let r = right.evaluate();
                l.combine(&r)
            }
        }
    }

    /// Combines this thunk with another without evaluating either
    #[inline]
    fn combine_with(&self, other: &Self) -> Self {
        LogThunk::Combine(Arc::new(self.clone()), Arc::new(other.clone()))
    }
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
    #[inline]
    pub fn new(log: W, value: A) -> Self {
        Writer {
            log_thunk: LogThunk::Value(log),
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
    /// This is where the log thunk is evaluated.
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
        (self.log_thunk.evaluate(), self.value)
    }

    /// Extracts just the value from the Writer, discarding the log.
    /// This is efficient as it doesn't evaluate the log thunk.
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
    /// This evaluates the log thunk.
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
        self.log_thunk.evaluate()
    }
}

impl<W, A> HKT for Writer<W, A> {
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
    fn pure_identity<B>(value: B) -> Self::Output<B> {
        Writer::new(W::empty(), value)
    }
}

impl<W: Monoid + Clone, A: Clone> Semigroup for Writer<W, A> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Writer {
            log_thunk: self.log_thunk.combine_with(&other.log_thunk),
            value: self.value,
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Writer {
            log_thunk: self.log_thunk.combine_with(&other.log_thunk),
            value: self.value.clone(),
        }
    }
}

impl<W: Monoid + Clone, A: Clone + Default> Monoid for Writer<W, A> {
    #[inline]
    fn empty() -> Self {
        Writer {
            log_thunk: LogThunk::Value(W::empty()),
            value: A::default(),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Functor for Writer<W, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Writer {
            log_thunk: self.log_thunk.clone(),
            value: f(&self.value),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        Writer {
            log_thunk: self.log_thunk,
            value: f(self.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Pure for Writer<W, A> {
    #[inline]
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Writer {
            log_thunk: LogThunk::Value(W::empty()),
            value: value.clone(),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Applicative for Writer<W, A> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Writer {
            log_thunk: self.log_thunk.combine_with(&f.log_thunk),
            value: (f.value)(&self.value),
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        Writer {
            log_thunk: self.log_thunk.combine_with(&b.log_thunk),
            value: f(&self.value, &b.value),
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        let combined_log = self
            .log_thunk
            .combine_with(&b.log_thunk)
            .combine_with(&c.log_thunk);
        Writer {
            log_thunk: combined_log,
            value: f(&self.value, &b.value, &c.value),
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        Writer {
            log_thunk: self.log_thunk.combine_with(&f.log_thunk),
            value: (f.value)(self.value),
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
    {
        Writer {
            log_thunk: self.log_thunk.combine_with(&b.log_thunk),
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
        F: Fn(Self::Source, B, C) -> D,
        Self: Sized,
    {
        let combined_log = self
            .log_thunk
            .combine_with(&b.log_thunk)
            .combine_with(&c.log_thunk);
        Writer {
            log_thunk: combined_log,
            value: f(self.value, b.value, c.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Monad for Writer<W, A> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        let result = f(&self.value);
        Writer {
            log_thunk: self.log_thunk.combine_with(&result.log_thunk),
            value: result.value,
        }
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        let inner: Self::Output<U> = self.value.clone().into();
        Writer {
            log_thunk: self.log_thunk.combine_with(&inner.log_thunk),
            value: inner.value,
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
        Self: Sized,
    {
        let result = f(self.value);
        Writer {
            log_thunk: self.log_thunk.combine_with(&result.log_thunk),
            value: result.value,
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized,
    {
        let inner: Self::Output<U> = self.value.into();
        Writer {
            log_thunk: self.log_thunk.combine_with(&inner.log_thunk),
            value: inner.value,
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Composable for Writer<W, A> {
    #[inline]
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }
}
