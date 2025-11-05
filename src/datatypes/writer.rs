//! # Writer Monad
//!
//! The Writer monad represents computations that produce a value along with an accumulated log.
//! It's a way to carry auxiliary data alongside the main computation result in a purely functional way.
//!
//! ## Quick Start
//!
//! Accumulate logs alongside computations:
//!
//! ```rust
//! use rustica::datatypes::writer::Writer;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::monad::Monad;
//!
//! // Create a Writer with a value and log (using String which implements Monoid)
//! let writer1 = Writer::new("Starting computation".to_string(), 42);
//!
//! // Transform the value while preserving the log
//! let doubled = writer1.fmap(|x| x * 2);
//! assert_eq!(doubled.clone().value(), 84);
//! assert_eq!(doubled.log(), "Starting computation");
//!
//! // Chain computations, combining logs
//! let result = Writer::new("Step 1".to_string(), 10)
//!     .bind(|x| Writer::new("Step 2".to_string(), x + 5))
//!     .bind(|x| Writer::new("Step 3".to_string(), x * 2));
//!
//! assert_eq!(result.clone().value(), 30);
//! assert_eq!(result.log(), "Step 1Step 2Step 3");
//!
//! // Add to log without changing the value
//! let with_log = Writer::<String, i32>::tell("Important note".to_string())
//!     .bind(|_| Writer::new("Final result".to_string(), 100));
//!
//! let (final_log, final_value) = with_log.run();
//! assert_eq!(final_value, 100);
//! assert_eq!(final_log, "Important noteFinal result");
//! ```
//!
//! ## Core Concepts
//!
//! - **Value and Log**: Each Writer computation produces both a primary value and a log/output
//! - **Log Accumulation**: When Writer computations are chained, their logs are combined using the monoid operation
//! - **Pure Functional Logging**: Allows for logging without side effects
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//!
//! - **Construction (new/tell)**: O(1) - Constant time to create a Writer instance
//! - **run/value/log**: O(1) - Constant time to extract values and logs
//! - **fmap**: O(n) - Where n is the complexity of the mapping function
//! - **bind**: O(m + n) - Where m is the log combination complexity (typically linear in log size)
//!   and n is the complexity of the binding function
//! - **apply/lift2/lift3**: O(m) - Where m is the log combination complexity
//!
//! ### Memory Usage
//!
//! - **Structure**: O(L + V) - Where L is the size of the log and V is the size of the value
//! - **Composition**: Each composition (via fmap/bind) creates new Writer instances but shares existing structure where possible
//! - **Implementation Detail**: Uses direct storage rather than functions to avoid stack issues with deeply nested structures
//!
//! ## Functional Programming Context
//!
//! In functional programming, the Writer monad solves the problem of producing output while maintaining referential
//! transparency. Instead of mutating a global log or using side effects, the Writer monad makes the output an
//! explicit part of the computation's return value.
//!
//! ## Type Class Implementations
//!
//! The Writer monad implements several important functional programming type classes:
//!
//! - **Functor**: Writer implements the Functor type class through its `fmap` method, which allows
//!   transforming the value inside the Writer context while preserving the accumulated log.
//!   - Implementation: `fmap :: (A -> B) -> Writer<W, A> -> Writer<W, B>`
//!   - This enables mapping operations over the contained value without affecting the log.
//!
//! - **Applicative**: Writer implements the Applicative type class through its `pure` and `apply` methods:
//!   - `pure`: Creates a Writer with the provided value and an empty log
//!     - Implementation: `pure :: A -> Writer<W, A>`
//!   - `apply`: Applies a function inside a Writer to a value inside another Writer, combining their logs
//!     - Implementation: `apply :: Writer<W, (A -> B)> -> Writer<W, A> -> Writer<W, B>`
//!
//! - **Monad**: Writer implements the Monad type class through its `bind` method, enabling sequential
//!   composition of Writer computations, where each computation can depend on the result of the previous
//!   and logs are combined.
//!   - Implementation: `bind :: Writer<W, A> -> (A -> Writer<W, B>) -> Writer<W, B>`
//!
//! - **MonadWriter**: Writer implements the MonadWriter type class through the utility functions:
//!   - `tell`: Creates a Writer with the given log and unit value
//!     - Implementation: `tell :: W -> Writer<W, ()>`
//!   - `listen`: Executes a Writer computation and returns both the original result and the accumulated log
//!     - Implementation: `listen :: Writer<W, A> -> Writer<W, (A, W)>`
//!   - `pass`: Executes a Writer computation that produces a value and a function to transform the log
//!     - Implementation: `pass :: Writer<W, (A, W -> W)> -> Writer<W, A>`
//!
//! - **Monoid**: When the value type is a Monoid, the Writer itself forms a Monoid
//!   - Implementation: `empty :: () -> Writer<W, A>` and `combine :: Writer<W, A> -> Writer<W, A> -> Writer<W, A>`
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! 1. **Identity Law**: `fmap(id) = id`
//! 2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
//!
//! ### Monad Laws
//!
//! 1. **Left Identity**: `pure(a).bind(f) = f(a)`
//! 2. **Right Identity**: `m.bind(pure) = m`
//! 3. **Associativity**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))`
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
//! The log type `W` must implement the Monoid trait, which provides:
//!
//! - An identity element (`empty`): The starting point for accumulation
//! - A binary operation (`combine`): How to combine two logs
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `new`, `tell`, `run`, `value`, and others.
//!
//! ```
//! use rustica::datatypes::writer::Writer;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::monad::Monad;
//!
//! #[derive(Clone)]
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
//! let double = |x: &i32| -> Writer<Log, i32> {
//!     Writer::new(Log(vec![format!("Doubled {} to {}", x, x * 2)]), x * 2)
//! };
//!
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
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
use quickcheck::{Arbitrary, Gen};

/// The Writer monad represents computations that produce a value along with an accumulated log.
///
/// # Performance Characteristics
///
/// ## Time Complexity
///
/// - **Construction**: O(1) - Creating a Writer instance takes constant time
/// - **Extraction (run/value)**: O(1) - Extracting values and logs takes constant time
/// - **Composition**: O(m) - Where m is the complexity of combining logs (typically linear with log size)
///
/// ## Memory Usage
///
/// - **Storage**: O(L + V) - Linear based on the size of the log (L) and value (V)
/// - **Thread Safety**: Safe to share between threads when `W` and `A` are `Send + Sync`
/// - **Implementation Detail**: Uses direct storage rather than function closures, avoiding
///   potential issues with deeply nested structures
///
/// # Type Class Instances
///
/// The Writer monad implements several type classes:
///
/// - **Functor**: Maps functions over the value using `fmap`
/// - **Applicative**: Applies functions contained in Writers to values in Writers
/// - **Monad**: Sequences Writer computations, combining their logs
/// - **Semigroup/Monoid**: When the value type is a Monoid
///
/// # Use Cases
///
/// The Writer monad is useful for:
/// - Logging operations in a purely functional way
/// - Accumulating data alongside computations
/// - Tracking the history of operations
/// - Building audit trails for computations
/// - Collecting metrics or statistics
///
/// # Type Parameters
///
/// - `W`: The log type, which must implement the Monoid trait
/// - `A`: The value type
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Writer<W, A> {
    /// The log accumulated during computation
    log: W,
    /// The value produced by the computation
    value: A,
}

impl<W: Monoid + Clone, A> Writer<W, A> {
    /// Creates a new Writer with the given value and log.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Constant time operation
    /// - **Memory Usage**: O(L + V) - Where L is the size of the log and V is the size of the value
    /// - **Thread Safety**: Safe to use across threads when `W` and `A` implement `Send + Sync`
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
    pub const fn new(log: W, value: A) -> Self {
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
    #[inline]
    pub const fn tell(log: W) -> Writer<W, ()> {
        Writer::new(log, ())
    }

    /// Extracts both the value and the log from the Writer.
    ///
    /// This method consumes the Writer and returns a tuple containing the log and value. It's the
    /// primary way to finalize a Writer computation and access both components of the result.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Constant time operation
    /// - **Memory Usage**: No additional memory is allocated beyond what's already in the Writer
    /// - **Ownership**: Transfers ownership of both the log and value to the caller
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
    #[inline]
    pub fn value(self) -> A {
        self.value
    }

    /// Creates a new Writer with the given value and an empty log.
    ///
    /// This is a convenience method that creates a Writer with a value and the empty monoid
    /// as the log.
    #[inline]
    pub fn pure_value(value: A) -> Self {
        Self::new(W::empty(), value)
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
    #[inline]
    pub fn log(self) -> W {
        self.log
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
}

impl<W: Monoid + Clone, A: Clone> Pure for Writer<W, A> {
    #[inline]
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Writer {
            log: W::empty(),
            value: value.clone(),
        }
    }

    #[inline]
    fn pure_owned<T>(value: T) -> Self::Output<T> {
        Writer {
            log: W::empty(),
            value,
        }
    }
}

impl<W: Monoid + Clone, A: Clone + Monoid> Semigroup for Writer<W, A> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Writer {
            log: self.log.combine_owned(other.log),
            value: self.value.combine_owned(other.value),
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Writer {
            log: self.log.combine(&other.log),
            value: self.value.combine(&other.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone + Monoid> Monoid for Writer<W, A> {
    #[inline]
    fn empty() -> Self {
        Writer {
            log: W::empty(),
            value: A::empty(),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Functor for Writer<W, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> B,
    {
        Writer {
            log: self.log.clone(),
            value: f(&self.value),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
    {
        Writer {
            log: self.log,
            value: f(self.value),
        }
    }
}

impl<W: Monoid + Clone, A: Clone> Applicative for Writer<W, A> {
    /// Applies a function stored in a Writer to a value stored in another Writer.
    ///
    /// This method is the core of the Applicative interface. It combines the logs of both Writers
    /// and applies the function from one Writer to the value in another.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 and L2 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create a Writer with a function and a log
    /// let add_five_fn = Writer::new(
    ///     Log(vec!["Function: add 5".to_string()]),
    ///     |x: &i32| x + 5
    /// );
    ///
    /// // Create a Writer with a value and a log
    /// let value_writer = Writer::new(
    ///     Log(vec!["Value: 10".to_string()]),
    ///     10
    /// );
    ///
    /// // Apply the function to the value, combining logs
    /// let result = Applicative::apply(&add_five_fn, &value_writer);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Function: add 5");
    /// assert_eq!(log.0[1], "Value: 10");
    /// ```
    #[inline]
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
    {
        Writer {
            log: self.log.combine(&value.log),
            value: (self.value)(&value.value),
        }
    }

    /// Applies a function to values from two Writer instances, combining their logs.
    ///
    /// This method allows you to combine two independent Writer computations using a binary function.
    /// It's useful for operations that need values from multiple Writers while preserving their logs.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 and L2 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create two Writers with different values
    /// let a = Writer::new(Log(vec!["Value a: 10".to_string()]), 10);
    /// let b = Writer::new(Log(vec!["Value b: 5".to_string()]), 5);
    ///
    /// // Combine them with a function that adds the values
    /// let result = Writer::<Log, i32>::lift2(|x, y| x + y, &a, &b);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Value a: 10");
    /// assert_eq!(log.0[1], "Value b: 5");
    /// ```
    #[inline]
    fn lift2<T, U, C, F>(f: F, fa: &Self::Output<T>, fb: &Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(&T, &U) -> C,
        T: Clone,
        U: Clone,
        C: Clone,
        Self: Sized,
    {
        Writer {
            log: fa.log.combine(&fb.log),
            value: f(&fa.value, &fb.value),
        }
    }

    /// Applies a function to values from three Writer instances, combining all their logs.
    ///
    /// This method allows you to combine three independent Writer computations using a ternary function.
    /// It's particularly useful for operations that need to gather values from multiple sources while
    /// preserving the logs from each computation.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + L3 + V) - Where L1, L2, and L3 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ## Basic Three-way Combination
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// let a = Writer::new(Log(vec!["Log A".to_string()]), 2);
    /// let b = Writer::new(Log(vec!["Log B".to_string()]), 3);
    /// let c = Writer::new(Log(vec!["Log C".to_string()]), 4);
    ///
    /// let result = Writer::<Log, i32>::lift3(|x, y, z| x * y * z, &a, &b, &c);
    /// let (log, value) = result.run();
    /// assert_eq!(value, 24);
    /// assert_eq!(log.0, vec!["Log A", "Log B", "Log C"]);
    /// ```
    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: &Self::Output<T>, fb: &Self::Output<U>, fc: &Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(&T, &U, &V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        Writer {
            log: fa.log.combine(&fb.log).combine(&fc.log),
            value: f(&fa.value, &fb.value, &fc.value),
        }
    }

    /// This method is similar to `apply` but it consumes the Writer instances, potentially allowing
    /// for more efficient memory usage in some cases.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 and L2 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    /// - **Ownership**: Consumes both Writer instances, which can be more efficient than cloning when used in a chain
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create a Writer with a function
    /// let add_five_fn = Writer::new(
    ///     Log(vec!["Function: add 5".to_string()]),
    ///     |x| x + 5
    /// );
    ///
    /// // Create a Writer with a value
    /// let value_writer = Writer::new(
    ///     Log(vec!["Value: 10".to_string()]),
    ///     10
    /// );
    ///
    /// // Apply the function to the value, consuming both Writers
    /// let result = Applicative::apply_owned(add_five_fn, value_writer);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Function: add 5");
    /// assert_eq!(log.0[1], "Value: 10");
    /// ```
    #[inline]
    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone,
    {
        Writer {
            log: self.log.combine_owned(value.log),
            value: (self.value)(value.value),
        }
    }

    /// Owned version of `lift2` which consumes the Writer instances.
    ///
    /// Applies a binary function to values from two Writer instances while combining their logs.
    /// This method consumes both Writer instances, potentially allowing for more efficient memory usage
    /// in some cases compared to the borrowing version.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 and L2 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    /// - **Ownership**: Consumes both Writer instances, which can be more efficient than borrowing when used in a chain
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create two Writers with different values
    /// let a = Writer::new(Log(vec!["Value a: 10".to_string()]), 10);
    /// let b = Writer::new(Log(vec!["Value b: 5".to_string()]), 5);
    ///
    /// // Combine them with a function that adds the values, consuming both Writers
    /// let result = Writer::<Log, i32>::lift2_owned(|x, y| x + y, a, b);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Value a: 10");
    /// assert_eq!(log.0[1], "Value b: 5");
    /// ```
    #[inline]
    fn lift2_owned<T, U, C, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(T, U) -> C,
        T: Clone,
        U: Clone,
        C: Clone,
        Self: Sized,
    {
        Writer {
            log: fa.log.combine_owned(fb.log),
            value: f(fa.value, fb.value),
        }
    }

    /// Owned version of `lift3` which consumes all three Writer instances.
    ///
    /// Applies a ternary function to values from three Writer instances while combining their logs.
    /// This method consumes all Writer instances, potentially allowing for more efficient memory usage
    /// compared to the borrowing version.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + L3 + V) - Where L1, L2, and L3 are the sizes of the input logs, and V is the size of the result value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    /// - **Ownership**: Consumes all three Writer instances, which can be more efficient than borrowing when used in a chain
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create three Writers with different values
    /// let a = Writer::new(Log(vec!["Value a: 10".to_string()]), 10);
    /// let b = Writer::new(Log(vec!["Value b: 5".to_string()]), 5);
    /// let c = Writer::new(Log(vec!["Value c: 2".to_string()]), 2);
    ///
    /// // Combine them with a function, consuming all Writers
    /// let result = Writer::<Log, i32>::lift3_owned(|x, y, z| x + y * z, a, b, c);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + (5 * 2) = 20
    /// assert_eq!(value, 20);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Value a: 10");
    /// assert_eq!(log.0[1], "Value b: 5");
    /// assert_eq!(log.0[2], "Value c: 2");
    /// ```
    #[inline]
    fn lift3_owned<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        let log = fa.log.combine_owned(fb.log).combine_owned(fc.log);
        let value = f(fa.value, fb.value, fc.value);
        Writer { log, value }
    }
}

impl<W: Monoid + Clone, A: Clone> Monad for Writer<W, A> {
    /// Sequences Writer computations, combining their logs.
    ///
    /// This method takes a Writer and a function that generates a new Writer based on the value of the first Writer.
    /// It runs both computations and combines their logs according to the Semigroup instance of the log type.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 is the size of the original log, L2 is the log from the function result,
    ///   and V is the size of the final value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monad::Monad;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Define a function to double a value and log the operation
    /// let double = |x: &i32| -> Writer<Log, i32> {
    ///     Writer::new(Log(vec![format!("Doubled {} to {}", x, x * 2)]), x * 2)
    /// };
    ///
    /// // Create an initial Writer
    /// let initial = Writer::new(Log(vec!["Starting with 3".to_string()]), 3);
    ///
    /// // Chain operations using bind
    /// let result = initial.bind(&double);
    ///
    /// // Extract final value and log
    /// let (log, value) = result.run();
    ///
    /// // Value should be 3 * 2 = 6
    /// assert_eq!(value, 6);
    ///
    /// // Log should contain both entries in order
    /// assert_eq!(log.0[0], "Starting with 3");
    /// assert_eq!(log.0[1], "Doubled 3 to 6");
    /// ```
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> Self::Output<U>,
    {
        let Writer { log, value } = f(&self.value);
        Writer {
            log: self.log.combine(&log),
            value,
        }
    }

    /// Owned version of `bind`, which consumes the Writer.
    ///
    /// This method is similar to `bind` but it consumes the Writer instance, potentially allowing
    /// for more efficient memory usage in some cases.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L + f) - Where L is the complexity of combining logs and f is the complexity of the function
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 is the size of the original log, L2 is the log from the function result,
    ///   and V is the size of the final value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monad::Monad;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// let initial = Writer::new(Log(vec!["Initial".to_string()]), 10);
    ///
    /// let result = initial.bind_owned(|x| {
    ///     Writer::new(Log(vec!["Processed".to_string()]), x * 2)
    /// });
    ///
    /// let (log, value) = result.run();
    /// assert_eq!(value, 20);
    /// assert_eq!(log.0, vec!["Initial".to_string(), "Processed".to_string()]);
    /// ```
    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        F: FnOnce(Self::Source) -> Self::Output<U>,
    {
        let result = f(self.value);
        Writer {
            log: self.log.combine_owned(result.log),
            value: result.value,
        }
    }

    /// Flattens a nested Writer structure by combining the logs.
    ///
    /// This method is used when you have a Writer containing another Writer and want to flatten
    /// the structure into a single Writer, combining the logs from both layers.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L) - Where L is the complexity of combining logs
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 is the size of the outer log, L2 is the size of the inner log,
    ///   and V is the size of the inner value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monad::Monad;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create a nested Writer structure
    /// let inner = Writer::new(Log(vec!["Inner log".to_string()]), 42);
    /// let outer = Writer::new(Log(vec!["Outer log".to_string()]), inner);
    ///
    /// // Flatten the nested structure
    /// let flattened = outer.join();
    ///
    /// // Check the result
    /// let (log, value) = flattened.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(log.0, vec!["Outer log".to_string(), "Inner log".to_string()]);
    /// ```
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
        U: Clone,
    {
        let inner: Self::Output<U> = self.value.clone().into();
        Writer {
            log: self.log.combine(&inner.log),
            value: inner.value,
        }
    }

    /// Owned version of `join`, which consumes the Writer.
    ///
    /// This method is similar to `join` but it consumes the Writer instance, potentially allowing
    /// for more efficient memory usage in some cases.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(L) - Where L is the complexity of combining logs
    /// - **Memory Usage**: O(L1 + L2 + V) - Where L1 is the size of the outer log, L2 is the size of the inner log,
    ///   and V is the size of the inner value
    /// - **Allocation**: Creates a new Writer instance with combined logs
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monad::Monad;
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
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         combined.extend(other.0);
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
    /// // Create a nested Writer structure
    /// let inner = Writer::new(Log(vec!["Inner log".to_string()]), 42);
    /// let outer = Writer::new(Log(vec!["Outer log".to_string()]), inner);
    ///
    /// // Flatten the nested structure using the owned version
    /// let flattened = outer.join_owned();
    ///
    /// // Check the result
    /// let (log, value) = flattened.run();
    /// assert_eq!(value, 42);
    /// assert_eq!(log.0, vec!["Outer log".to_string(), "Inner log".to_string()]);
    /// ```
    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized,
    {
        let inner: Self::Output<U> = self.value.into();
        Writer {
            log: self.log.combine_owned(inner.log),
            value: inner.value,
        }
    }
}

impl<W, A> IntoIterator for Writer<W, A> {
    type Item = A;
    type IntoIter = std::option::IntoIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        Some(self.value).into_iter()
    }
}

impl<'a, W, A> IntoIterator for &'a Writer<W, A> {
    type Item = &'a A;
    type IntoIter = std::slice::Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        std::slice::from_ref(&self.value).iter()
    }
}

impl<'a, W, A> IntoIterator for &'a mut Writer<W, A> {
    type Item = &'a mut A;
    type IntoIter = std::slice::IterMut<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        std::slice::from_mut(&mut self.value).iter_mut()
    }
}

impl<E, A> Arbitrary for Writer<E, A>
where
    E: Monoid + Arbitrary,
    A: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = A::arbitrary(g);
        let y = E::arbitrary(g);
        Writer::new(y, x)
    }
}
