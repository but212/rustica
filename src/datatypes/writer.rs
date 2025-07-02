//! # Writer Monad
//!
//! The Writer monad represents computations that produce a value along with an accumulated log.
//! It's a way to carry auxiliary data alongside the main computation result in a purely functional way.
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
//! The Writer monad implements several functional programming abstractions:
//!
//! - **Functor**: Via the `fmap` method, allowing transformation of the value
//! - **Applicative**: Through the `combine` and `lift2` methods
//! - **Monad**: With the `bind` method for sequencing operations
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! 1. **Identity Law**: `fmap(id) = id`
//!    ```rust
//!    # use rustica::datatypes::writer::Writer;
//!    # use rustica::traits::monoid::Monoid;
//!    # use rustica::traits::semigroup::Semigroup;
//!    # use rustica::traits::functor::Functor;
//!    #
//!    # #[derive(Clone, Debug, PartialEq)]
//!    # struct Log(Vec<String>);
//!    #
//!    # impl Semigroup for Log {
//!    #     fn combine(&self, other: &Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    #
//!    #     fn combine_owned(self, other: Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    # }
//!    #
//!    # impl Monoid for Log {
//!    #     fn empty() -> Self {
//!    #         Log(Vec::new())
//!    #     }
//!    # }
//!    
//!    let writer = Writer::new(Log(vec!["test".to_string()]), 42);
//!    let id = |x| x;
//!    
//!    assert_eq!(writer.clone().fmap_owned(id), writer);
//!    ```
//!
//!    2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
//!    ```rust
//!    # use rustica::datatypes::writer::Writer;
//!    # use rustica::traits::monoid::Monoid;
//!    # use rustica::traits::semigroup::Semigroup;
//!    # use rustica::traits::functor::Functor;
//!    #
//!    # #[derive(Clone, Debug, PartialEq)]
//!    # struct Log(Vec<String>);
//!    #
//!    # impl Semigroup for Log {
//!    #     fn combine(&self, other: &Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    #
//!    #     fn combine_owned(self, other: Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    # }
//!    #
//!    # impl Monoid for Log {
//!    #     fn empty() -> Self {
//!    #         Log(Vec::new())
//!    #     }
//!    # }
//!    
//!    let writer = Writer::new(Log(vec!["test".to_string()]), 5);
//!    let f = |x: i32| x * 3;
//!    let g = |x: i32| x + 2;
//!    
//!    // fmap(f . g)
//!    let composed = writer.clone().fmap_owned(|x| f(g(x)));
//!    
//!    // fmap(f) . fmap(g)
//!    let chained = writer.clone().fmap_owned(g).fmap_owned(f);
//!    
//!    assert_eq!(composed, chained);
//!    ```
//!
//! ### Monad Laws
//!
//! 1. **Left Identity**: `pure(a).bind(f) = f(a)`
//!    ```rust
//!    # use rustica::datatypes::writer::Writer;
//!    # use rustica::traits::monoid::Monoid;
//!    # use rustica::traits::semigroup::Semigroup;
//!    # use rustica::traits::monad::Monad;
//!    # use rustica::traits::pure::Pure;
//!    #
//!    # #[derive(Clone, Debug, PartialEq)]
//!    # struct Log(Vec<String>);
//!    #
//!    # impl Semigroup for Log {
//!    #     fn combine(&self, other: &Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    #
//!    #     fn combine_owned(self, other: Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    # }
//!    #
//!    # impl Monoid for Log {
//!    #     fn empty() -> Self {
//!    #         Log(Vec::new())
//!    #     }
//!    # }
//!    
//!    let value = 10;
//!    let f = |x: i32| Writer::new(Log(vec![format!("Value: {}", x)]), x * 2);
//!    
//!    let left_side = Writer::<Log, i32>::pure_owned(value).bind_owned(f);
//!    let right_side = f(value);
//!    
//!    assert_eq!(left_side, right_side);
//!    ```
//!
//! 2. **Right Identity**: `m.bind(pure) = m`
//!    ```rust
//!    # use rustica::datatypes::writer::Writer;
//!    # use rustica::traits::monoid::Monoid;
//!    # use rustica::traits::semigroup::Semigroup;
//!    # use rustica::traits::monad::Monad;
//!    # use rustica::traits::pure::Pure;
//!    #
//!    # #[derive(Clone, Debug, PartialEq)]
//!    # struct Log(Vec<String>);
//!    #
//!    # impl Semigroup for Log {
//!    #     fn combine(&self, other: &Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    #
//!    #     fn combine_owned(self, other: Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    # }
//!    #
//!    # impl Monoid for Log {
//!    #     fn empty() -> Self {
//!    #         Log(Vec::new())
//!    #     }
//!    # }
//!    
//!    let m = Writer::new(Log(vec!["log entry".to_string()]), 42);
//!    let right_side = m.clone().bind_owned(Writer::<Log, i32>::pure_owned);
//!    
//!    assert_eq!(m, right_side);
//!    ```
//!
//! 3. **Associativity**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))`
//!    ```rust
//!    # use rustica::datatypes::writer::Writer;
//!    # use rustica::traits::monoid::Monoid;
//!    # use rustica::traits::semigroup::Semigroup;
//!    # use rustica::traits::monad::Monad;
//!    #
//!    # #[derive(Clone, Debug, PartialEq)]
//!    # struct Log(Vec<String>);
//!    #
//!    # impl Semigroup for Log {
//!    #     fn combine(&self, other: &Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    #
//!    #     fn combine_owned(self, other: Self) -> Self {
//!    #         let mut combined = self.0.clone();
//!    #         combined.extend(other.0.clone());
//!    #         Log(combined)
//!    #     }
//!    # }
//!    #
//!    # impl Monoid for Log {
//!    #     fn empty() -> Self {
//!    #         Log(Vec::new())
//!    #     }
//!    # }
//!    
//!    let m = Writer::new(Log(vec!["initial".to_string()]), 5);
//!    let f = |x: i32| Writer::new(Log(vec![format!("f: {}", x)]), x * 2);
//!    let g = |x: i32| Writer::new(Log(vec![format!("g: {}", x)]), x + 10);
//!    
//!    let left_side = m.clone().bind_owned(f).bind_owned(g);
//!    
//!    let right_side = m.clone().bind_owned(|x| {
//!        f(x).bind_owned(g)
//!    });
//!    
//!    assert_eq!(left_side, right_side);
//!    ```
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
//! ### Iterator Example
//!
//! Iterating over a Writer yields its value once (if present), ignoring the log.
//!
//! ```rust
//! use rustica::datatypes::writer::Writer;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Define a simple log type
//! #[derive(Clone, Debug, PartialEq)]
//! struct Log(String);
//!
//! impl Semigroup for Log {
//!     fn combine(&self, other: &Self) -> Self {
//!         Log(self.0.clone() + &other.0)
//!     }
//!
//!     fn combine_owned(self, other: Self) -> Self {
//!         Log(self.0 + &other.0)
//!     }
//! }
//!
//! impl Monoid for Log {
//!     fn empty() -> Self {
//!         Log(String::new())
//!     }
//! }
//!
//! let writer = Writer::new(Log("log".to_string()), 42);
//! let mut iter = writer.into_iter();
//! assert_eq!(iter.next(), Some(42));
//! assert_eq!(iter.next(), None);
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
#[cfg(feature = "develop")]
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
    /// ## Basic Usage
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
    ///
    /// ## As A Starting Point For Computation Chains
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
    /// // Define some operations
    /// let double = |x: &i32| -> Writer<Log, i32> {
    ///     Writer::new(Log(vec![format!("Doubled {} to {}", x, x * 2)]), x * 2)
    /// };
    ///
    /// // Start a computation chain
    /// let computation = Writer::new(Log(vec!["Starting with 5".to_string()]), 5);
    /// let result = computation.bind(&double);
    ///
    /// // Run the computation to get the final value and combined log
    /// let (log, value) = result.run();
    ///
    /// assert_eq!(value, 10); // 5 * 2 = 10
    /// assert_eq!(log.0.len(), 2); // Two log entries
    /// ```
    ///
    /// ## With Different Log Types
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// // A more complex log type for collecting metrics
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Metrics(HashMap<String, i32>);
    ///
    /// impl Semigroup for Metrics {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         for (key, &value) in &other.0 {
    ///             *combined.entry(key.clone()).or_insert(0) += value;
    ///         }
    ///         Metrics(combined)
    ///     }
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         for (key, value) in other.0 {
    ///             *combined.entry(key).or_insert(0) += value;
    ///         }
    ///         Metrics(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Metrics {
    ///     fn empty() -> Self {
    ///         Metrics(HashMap::new())
    ///     }
    /// }
    ///
    /// // Create initial metrics
    /// let mut metrics = HashMap::new();
    /// metrics.insert("operations".to_string(), 1);
    ///
    /// // Create a writer with a value and metrics
    /// let writer = Writer::new(Metrics(metrics), "result");
    ///
    /// // Run the computation
    /// let (log, value) = writer.run();
    ///
    /// assert_eq!(value, "result");
    /// assert_eq!(log.0.get("operations"), Some(&1));
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
    /// ## Basic Usage
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
    ///
    /// ## Finalizing a Computation Chain
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
    /// // Define a multi-step computation
    /// let step1 = |x: &i32| -> Writer<Log, i32> {
    ///     Writer::new(Log(vec![format!("Step 1: {} -> {}", x, x + 10)]), x + 10)
    /// };
    ///
    /// let step2 = |x: &i32| -> Writer<Log, i32> {
    ///     Writer::new(Log(vec![format!("Step 2: {} -> {}", x, x * 2)]), x * 2)
    /// };
    ///
    /// // Chain the computations and then extract the final result
    /// let computation = Writer::new(Log(vec!["Starting with 5".to_string()]), 5);
    /// let result = computation.bind(&step1).bind(&step2);
    ///
    /// let (log, final_value) = result.run();
    ///
    /// // Check the final value: (5 + 10) * 2 = 30
    /// assert_eq!(final_value, 30);
    ///
    /// // Check that the log contains entries from all three steps
    /// assert_eq!(log.0.len(), 3);
    /// assert_eq!(log.0[0], "Starting with 5");
    /// assert_eq!(log.0[1], "Step 1: 5 -> 15");
    /// assert_eq!(log.0[2], "Step 2: 15 -> 30");
    /// ```
    ///
    /// ## Processing the Final Result
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
    /// // Create a writer with some value and logs
    /// let writer = Writer::new(Log(vec!["Computation started".to_string(), "Processing data".to_string()]), 42);
    ///
    /// // Run the computation and process both the log and value
    /// let (log, value) = writer.run();
    ///
    /// // Format the logs for display
    /// let formatted_logs = log.0.iter()
    ///     .enumerate()
    ///     .map(|(i, entry)| format!("{}: {}", i + 1, entry))
    ///     .collect::<Vec<_>>()
    ///     .join("\n");
    ///
    /// // Process the value
    /// let result_message = format!("Final result: {}", value);
    ///
    /// // Verify the formatting worked correctly
    /// assert_eq!(formatted_logs, "1: Computation started\n2: Processing data");
    /// assert_eq!(result_message, "Final result: 42");
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

    #[inline]
    fn pure_identity<B>(value: B) -> Self::Output<B> {
        Writer::new(W::empty(), value)
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
    /// ## Basic Function Application
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
    /// let result = value_writer.apply(&add_five_fn);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Value: 10");
    /// assert_eq!(log.0[1], "Function: add 5");
    /// ```
    ///
    /// ## Application with Multiple Functions
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
    /// // Create a Writer with a value
    /// let value = Writer::new(Log(vec!["Starting value: 5".to_string()]), 5);
    ///
    /// // Create Writers with different functions
    /// let double = Writer::new(Log(vec!["Function: double".to_string()]), |x: &i32| x * 2);
    /// let add_one = Writer::new(Log(vec!["Function: add one".to_string()]), |x: &i32| x + 1);
    ///
    /// // Apply functions in sequence
    /// let result = value.apply(&double).apply(&add_one);
    ///
    /// // Extract the result
    /// let (log, final_value) = result.run();
    ///
    /// // Check the value: (5 * 2) + 1 = 11
    /// assert_eq!(final_value, 11);
    ///
    /// // Check that logs were combined in order
    /// assert_eq!(log.0[0], "Starting value: 5");
    /// assert_eq!(log.0[1], "Function: double");
    /// assert_eq!(log.0[2], "Function: add one");
    /// ```
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Writer {
            log: self.log.combine(&f.log),
            value: (f.value)(&self.value),
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
    /// let result = a.lift2(&b, |x, y| x + y);
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
    ///
    /// ## Complex Data Combination
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
    /// use std::collections::HashMap;
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
    /// // Create two Writers with different data types
    /// let user_id = Writer::new(Log(vec!["Found user ID".to_string()]), 42);
    /// let user_name = Writer::new(Log(vec!["Retrieved user name".to_string()]), "Alice".to_string());
    ///
    /// // Combine them to create a user record
    /// let user = user_id.lift2(&user_name, |&id, name| {
    ///     let mut user = HashMap::new();
    ///     user.insert("id".to_string(), id.to_string());
    ///     user.insert("name".to_string(), name.clone());
    ///     user
    /// });
    ///
    /// // Extract the result
    /// let (log, user_record) = user.run();
    ///
    /// // Check the user record
    /// assert_eq!(user_record.get("id").unwrap(), "42");
    /// assert_eq!(user_record.get("name").unwrap(), "Alice");
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Found user ID");
    /// assert_eq!(log.0[1], "Retrieved user name");
    /// ```
    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(&Self::Source, &B) -> C,
    {
        Writer {
            log: self.log.combine(&b.log),
            value: f(&self.value, &b.value),
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
    /// let result = a.lift3(&b, &c, |x, y, z| x * y * z);
    /// let (log, value) = result.run();
    /// assert_eq!(value, 24);
    /// assert_eq!(log.0, vec!["Log A", "Log B", "Log C"]);
    /// ```
    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: FnOnce(&Self::Source, &B, &C) -> D,
    {
        Writer {
            log: self.log.combine(&b.log).combine(&c.log),
            value: f(&self.value, &b.value, &c.value),
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
    /// // Create three Writers with different values
    /// let a = Writer::new(Log(vec!["Value a: 10".to_string()]), 10);
    /// let b = Writer::new(Log(vec!["Value b: 5".to_string()]), 5);
    /// let c = Writer::new(Log(vec!["Value c: 2".to_string()]), 2);
    ///
    /// // Combine them with a function
    /// let result = a.lift3(&b, &c, |x, y, z| x + y * z);
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
    ///
    /// ## Combining Complex Data
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
    /// use std::collections::HashMap;
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
    /// // Create Writers with different user data components
    /// let user_id = Writer::new(Log(vec!["Retrieved user ID".to_string()]), 42);
    /// let user_name = Writer::new(Log(vec!["Retrieved user name".to_string()]), "Alice".to_string());
    /// let user_role = Writer::new(Log(vec!["Retrieved user role".to_string()]), "Admin".to_string());
    ///
    /// // Combine all components to create a complete user profile
    /// let user_profile = user_id.lift3(&user_name, &user_role, |&id, name, role| {
    ///     let mut profile = HashMap::new();
    ///     profile.insert("id".to_string(), id.to_string());
    ///     profile.insert("name".to_string(), name.clone());
    ///     profile.insert("role".to_string(), role.clone());
    ///     profile
    /// });
    ///
    /// // Extract the result
    /// let (log, profile) = user_profile.run();
    ///
    /// // Check the user profile
    /// assert_eq!(profile.get("id").unwrap(), "42");
    /// assert_eq!(profile.get("name").unwrap(), "Alice");
    /// assert_eq!(profile.get("role").unwrap(), "Admin");
    ///
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
    /// let result = value_writer.apply_owned(add_five_fn);
    ///
    /// // Extract the result
    /// let (log, value) = result.run();
    ///
    /// // Check the value: 10 + 5 = 15
    /// assert_eq!(value, 15);
    ///
    /// // Check that logs were combined
    /// assert_eq!(log.0[0], "Value: 10");
    /// assert_eq!(log.0[1], "Function: add 5");
    /// ```
    ///
    /// ## In A Processing Chain
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
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
    /// // Create a starting value
    /// let start = Writer::new(Log(vec!["Start: 5".to_string()]), 5);
    ///
    /// // Create a function wrapped in a Writer
    /// let double = Writer::new(Log(vec!["Doubling".to_string()]), |x| x * 2);
    ///
    /// // Apply the function, consuming both Writers
    /// let intermediate = start.apply_owned(double);
    ///
    /// // Create another function
    /// let add_three = Writer::new(Log(vec!["Adding 3".to_string()]), |x| x + 3);
    ///
    /// // Apply the second function, again consuming both Writers
    /// let result = intermediate.apply_owned(add_three);
    ///
    /// // Extract the final result
    /// let (log, value) = result.run();
    ///
    /// // Value should be (5 * 2) + 3 = 13
    /// assert_eq!(value, 13);
    ///
    /// // Check combined logs
    /// assert_eq!(log.0[0], "Start: 5");
    /// assert_eq!(log.0[1], "Doubling");
    /// assert_eq!(log.0[2], "Adding 3");
    /// ```
    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
    {
        Writer {
            log: self.log.combine_owned(f.log),
            value: (f.value)(self.value),
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
    /// ## Basic Binary Operation
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
    /// let result = a.lift2_owned(b, |x, y| x + y);
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
    ///
    /// ## In A Processing Pipeline
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::functor::Functor;
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
    /// // Create a Writer for calculating tax
    /// let price = Writer::new(Log(vec!["Base price: $100".to_string()]), 100);
    /// let tax_rate = Writer::new(Log(vec!["Tax rate: 8%".to_string()]), 0.08);
    ///
    /// // Calculate total price with tax
    /// let total_with_tax = price.lift2_owned(tax_rate, |p, rate| {
    ///     let tax_amount = p * rate;
    ///     p + tax_amount
    /// });
    ///
    /// // Format the result for display
    /// let formatted = total_with_tax.fmap(|value| format!("${:.2}", value));
    ///
    /// // Extract the result
    /// let (log, value) = formatted.run();
    ///
    /// // Check the formatted value: $100 + ($100 * 0.08) = $108.00
    /// assert_eq!(value, "$108.00");
    ///
    /// // Check the logs
    /// assert_eq!(log.0[0], "Base price: $100");
    /// assert_eq!(log.0[1], "Tax rate: 8%");
    /// ```
    #[inline]
    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(Self::Source, B) -> C,
    {
        Writer {
            log: self.log.combine_owned(b.log),
            value: f(self.value, b.value),
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
    /// // Create three Writers with different values
    /// let a = Writer::new(Log(vec!["Value a: 10".to_string()]), 10);
    /// let b = Writer::new(Log(vec!["Value b: 5".to_string()]), 5);
    /// let c = Writer::new(Log(vec!["Value c: 2".to_string()]), 2);
    ///
    /// // Combine them with a function, consuming all Writers
    /// let result = a.lift3_owned(b, c, |x, y, z| x + y * z);
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
    ///
    /// ## Building a Complex Structure
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
    /// // Define a simple order structure
    /// #[derive(Debug, PartialEq)]
    /// struct Order {
    ///     id: u32,
    ///     product: String,
    ///     quantity: u32,
    /// }
    ///
    /// // Create three Writers with order components
    /// let order_id = Writer::new(Log(vec!["Generated order ID: 1001".to_string()]), 1001u32);
    /// let product = Writer::new(Log(vec!["Selected product: Keyboard".to_string()]), "Keyboard".to_string());
    /// let quantity = Writer::new(Log(vec!["Set quantity: 2".to_string()]), 2u32);
    ///
    /// // Combine them to create an order, consuming all Writers
    /// let order = order_id.lift3_owned(product, quantity, |id, product, quantity| {
    ///     Order { id, product, quantity }
    /// });
    ///
    /// // Extract the result
    /// let (log, order_value) = order.run();
    ///
    /// // Check the order values
    /// assert_eq!(order_value.id, 1001);
    /// assert_eq!(order_value.product, "Keyboard");
    /// assert_eq!(order_value.quantity, 2);
    ///
    /// // Check the logs
    /// assert_eq!(log.0[0], "Generated order ID: 1001");
    /// assert_eq!(log.0[1], "Selected product: Keyboard");
    /// assert_eq!(log.0[2], "Set quantity: 2");
    /// ```
    #[inline]
    fn lift3_owned<B, C, D, F>(
        self, b: Self::Output<B>, c: Self::Output<C>, f: F,
    ) -> Self::Output<D>
    where
        F: FnOnce(Self::Source, B, C) -> D,
    {
        let log = self.log.combine_owned(b.log).combine_owned(c.log);
        let value = f(self.value, b.value, c.value);
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
    /// ## Basic Chaining of Computations
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
    /// // Define a function to add 5 to a value and log the operation
    /// let add_five = |x: &i32| -> Writer<Log, i32> {
    ///     Writer::new(Log(vec![format!("Added 5 to {} to get {}", x, x + 5)]), x + 5)
    /// };
    ///
    /// // Create an initial Writer
    /// let initial = Writer::new(Log(vec!["Starting with 3".to_string()]), 3);
    ///
    /// // Chain operations using bind
    /// let result = initial.bind(&double).bind(&add_five);
    ///
    /// // Extract final value and log
    /// let (log, value) = result.run();
    ///
    /// // Value should be (3 * 2) + 5 = 11
    /// assert_eq!(value, 11);
    ///
    /// // Log should contain all three entries in order
    /// assert_eq!(log.0[0], "Starting with 3");
    /// assert_eq!(log.0[1], "Doubled 3 to 6");
    /// assert_eq!(log.0[2], "Added 5 to 6 to get 11");
    /// ```
    ///
    /// ## Multi-step Data Processing
    ///
    /// ```rust
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monad::Monad;
    /// use std::collections::HashMap;
    ///
    /// // A metrics log type for collecting statistics
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Metrics(HashMap<String, i32>);
    ///
    /// impl Semigroup for Metrics {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         let mut combined = self.0.clone();
    ///         for (key, &value) in &other.0 {
    ///             *combined.entry(key.clone()).or_insert(0) += value;
    ///         }
    ///         Metrics(combined)
    ///     }
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         let mut combined = self.0;
    ///         for (key, value) in other.0 {
    ///             *combined.entry(key).or_insert(0) += value;
    ///         }
    ///         Metrics(combined)
    ///     }
    /// }
    ///
    /// impl Monoid for Metrics {
    ///     fn empty() -> Self {
    ///         Metrics(HashMap::new())
    ///     }
    /// }
    ///
    /// // Define a data processing pipeline
    /// let validate = |data: &String| -> Writer<Metrics, String> {
    ///     let mut metrics = HashMap::new();
    ///     metrics.insert("validation_count".to_string(), 1);
    ///     Writer::new(Metrics(metrics), data.clone())
    /// };
    ///
    /// let normalize = |data: &String| -> Writer<Metrics, String> {
    ///     let mut metrics = HashMap::new();
    ///     metrics.insert("normalize_count".to_string(), 1);
    ///     let result = data.to_lowercase();
    ///     Writer::new(Metrics(metrics), result)
    /// };
    ///
    /// let tokenize = |data: &String| -> Writer<Metrics, Vec<String>> {
    ///     let mut metrics = HashMap::new();
    ///     metrics.insert("tokenize_count".to_string(), 1);
    ///     let tokens = data.split_whitespace().map(|s| s.to_string()).collect();
    ///     Writer::new(Metrics(metrics), tokens)
    /// };
    ///
    /// // Process some input data through the pipeline
    /// let input = Writer::new(Metrics(HashMap::new()), "Hello World".to_string());
    /// let processed = input.bind(&validate).bind(&normalize).bind(&tokenize);
    ///
    /// // Extract results
    /// let (metrics, tokens) = processed.run();
    ///
    /// // Check tokens
    /// assert_eq!(tokens, vec!["hello", "world"]);
    ///
    /// // Check metrics
    /// assert_eq!(*metrics.0.get("validation_count").unwrap(), 1);
    /// assert_eq!(*metrics.0.get("normalize_count").unwrap(), 1);
    /// assert_eq!(*metrics.0.get("tokenize_count").unwrap(), 1);
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

#[cfg(feature = "develop")]
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
