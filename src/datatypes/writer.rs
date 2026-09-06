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
//! assert_eq!(doubled.clone().unwrap(), 84);
//! assert_eq!(doubled.log(), "Starting computation");
//!
//! // Chain computations, combining logs
//! let result = Writer::new("Step 1".to_string(), 10)
//!     .bind(|x| Writer::new("Step 2".to_string(), x + 5))
//!     .bind(|x| Writer::new("Step 3".to_string(), x * 2));
//!
//! assert_eq!(result.clone().unwrap(), 30);
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
//! - **Logging helpers**: This module provides [`Writer::tell`] for adding log output without producing a
//!   meaningful value.
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
//! The log type must implement [`Monoid`]. The `tests` module exercises custom log types,
//! ordered accumulation, and chained computations.
use crate::traits::applicative::Applicative;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

/// The Writer monad represents computations that produce a value along with an accumulated log.
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
    ///     fn combine(mut self, other: Self) -> Self {
    ///         self.0.extend(other.0);
    ///         self
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
    ///     fn combine(mut self, other: Self) -> Self {
    ///         self.0.extend(other.0);
    ///         self
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
    ///     fn combine(mut self, other: Self) -> Self {
    ///         self.0.extend(other.0);
    ///         self
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
    /// This method does not consume the Writer. It returns a clone of the contained value.
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
    ///     fn combine(mut self, other: Self) -> Self {
    ///         self.0.extend(other.0);
    ///         self
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
    /// let value = writer.unwrap();
    /// assert_eq!(value, 42);
    /// ```
    #[inline]
    pub fn unwrap(self) -> A {
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
    /// This method consumes the Writer.
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
    ///     fn combine(mut self, other: Self) -> Self {
    ///         self.0.extend(other.0);
    ///         self
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

impl<W: Monoid, A> Pure for Writer<W, A> {
    #[inline]
    fn pure<T>(value: T) -> Self::Output<T> {
        Writer {
            log: W::empty(),
            value,
        }
    }
}

impl<W: Monoid, A: Semigroup> Semigroup for Writer<W, A> {
    #[inline]
    fn combine(self, other: Self) -> Self {
        Writer {
            log: self.log.combine(other.log),
            value: self.value.combine(other.value),
        }
    }
}

impl<W: Monoid, A: Monoid> Monoid for Writer<W, A> {
    #[inline]
    fn empty() -> Self {
        Writer {
            log: W::empty(),
            value: A::empty(),
        }
    }
}

impl<W, A> Functor for Writer<W, A> {
    #[inline]
    fn fmap<B, F>(self, mut f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        Writer {
            log: self.log,
            value: f(self.value),
        }
    }
}

impl<W: Monoid, A> Applicative for Writer<W, A> {
    #[inline]
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
    {
        Writer {
            log: self.log.combine(value.log),
            value: (self.value)(value.value),
        }
    }

    #[inline]
    fn lift2<T, U, C, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(T, U) -> C,
        T: Clone,
        U: Clone,
    {
        Writer {
            log: fa.log.combine(fb.log),
            value: f(fa.value, fb.value),
        }
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
    {
        Writer {
            log: fa.log.combine(fb.log).combine(fc.log),
            value: f(fa.value, fb.value, fc.value),
        }
    }
}

impl<W: Monoid, A> Monad for Writer<W, A> {
    #[inline]
    fn bind<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        let result = f(self.value);
        Writer {
            log: self.log.combine(result.log),
            value: result.value,
        }
    }

    #[inline]
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        let inner: Self::Output<U> = self.value.into();
        Writer {
            log: self.log.combine(inner.log),
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

#[cfg(any(test, feature = "quickcheck"))]
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

#[cfg(test)]
mod tests {
    use super::Writer;
    use crate::datatypes::wrapper::sum::Sum;
    use crate::prelude::*;

    #[derive(Clone, Debug, PartialEq, Default)]
    struct Log(Vec<String>);

    impl Semigroup for Log {
        fn combine(mut self, other: Self) -> Self {
            self.0.extend(other.0);
            self
        }
    }

    impl Monoid for Log {
        fn empty() -> Self {
            Log(Vec::new())
        }
    }

    #[test]
    fn test_writer_lifecycle_and_mapping() {
        let w1 = Writer::new(Log(vec!["init".into()]), 42);
        let w_pure = Writer::<Log, _>::pure_value(100);
        assert_eq!(w1.clone().run(), (Log(vec!["init".into()]), 42));
        assert_eq!(w_pure.run(), (Log::empty(), 100));
        assert_eq!(w1.fmap(|x| x * 2).run(), (Log(vec!["init".into()]), 84));
    }

    #[test]
    fn test_writer_accumulation_modes() {
        let w_fn = Writer::new(Log(vec!["f".into()]), |x: i32| x * 2);
        let w_val = Writer::new(Log(vec!["v".into()]), 21);
        assert_eq!(
            w_fn.apply(w_val).run(),
            (Log(vec!["f".into(), "v".into()]), 42)
        );

        let monad_res = Writer::new(Log(vec!["step1".into()]), 10)
            .bind(|x| Writer::new(Log(vec![format!("step2:{x}")]), x + 5));
        assert_eq!(
            monad_res.run(),
            (Log(vec!["step1".into(), "step2:10".into()]), 15)
        );
    }

    #[test]
    fn test_writer_requirements_example_flow() {
        let double = |x: i32| -> Writer<Log, i32> {
            Writer::new(Log(vec![format!("Doubled {x} to {}", x * 2)]), x * 2)
        };
        let add_ten = |x: i32| -> Writer<Log, i32> {
            Writer::new(Log(vec![format!("Added 10 to {x} to {}", x + 10)]), x + 10)
        };

        let computation = Writer::new(Log(vec!["Starting with 5".to_string()]), 5);
        let (log, value) = computation.bind(double).bind(add_ten).run();

        assert_eq!(value, 20);
        assert_eq!(log.0.len(), 3);
        assert_eq!(
            log,
            Log(vec![
                "Starting with 5".into(),
                "Doubled 5 to 10".into(),
                "Added 10 to 10 to 20".into(),
            ])
        );
    }

    #[test]
    fn test_writer_composition_scenarios() {
        let pipeline = Writer::<Log, _>::pure_value(5)
            .bind(|n| Writer::new(Log(vec!["start".into()]), n))
            .bind(|n| Writer::new(Log(vec!["double".into()]), n * 2))
            .bind(|n| Writer::new(Log(vec!["plus10".into()]), n + 10))
            .fmap(|n| n * 2);
        let (log, val) = pipeline.run();
        assert_eq!(val, 40);
        assert_eq!(log.0.len(), 3);

        let w1 = Writer::new(Log(vec!["l1".into()]), Sum(15));
        let w2 = Writer::new(Log(vec!["l2".into()]), Sum(27));
        assert_eq!(
            w1.combine(w2).run(),
            (Log(vec!["l1".into(), "l2".into()]), Sum(42))
        );
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_tests {
    use super::Writer;
    use crate::traits::{monoid::Monoid, semigroup::Semigroup};

    #[derive(Clone, Debug, PartialEq, Default)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    struct Log(Vec<String>);

    impl Semigroup for Log {
        fn combine(mut self, other: Self) -> Self {
            self.0.extend(other.0);
            self
        }
    }
    impl Monoid for Log {
        fn empty() -> Self {
            Log(Vec::new())
        }
    }

    #[test]
    fn writer_round_trips_through_serde() {
        let writer = Writer::new(Log(vec!["log".into()]), 42);
        let json = serde_json::to_string(&writer).unwrap();
        let back: Writer<Log, i32> = serde_json::from_str(&json).unwrap();
        assert_eq!(writer, back);
    }
}
