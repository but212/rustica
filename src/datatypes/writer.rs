use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::monoid::Monoid;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::fntype::{FnType, FnTrait};

/// The writer monad.
///
/// # Type Parameters
/// * `W` - The log type, must implement the `Monoid` trait.
/// * `A` - The output type.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::writer::Writer;
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
///
/// #[derive(Clone, PartialEq, Eq, Debug, Default)]
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
/// let writer = Writer::new(42, Log(vec!["Initial log".to_string()]));
/// let (value, log) = writer.run();
///
/// assert_eq!(value, 42);
/// assert_eq!(log, Log(vec!["Initial log".to_string()]));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    /// The function that performs the computation and returns the result along with the log.
    run_writer: FnType<(), (A, W)>
}

impl<W, A> Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    /// Creates a new `Writer` with the given value and log.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in the `Writer`.
    /// * `log` - The initial log to be associated with the `Writer`.
    ///
    /// # Returns
    ///
    /// A new `Writer` instance containing the provided value and log.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let writer = Writer::new(42, vec!["Initial log".to_string()]);
    /// let (value, log) = writer.run();
    ///
    /// assert_eq!(value, 42);
    /// assert_eq!(log, vec!["Initial log".to_string()]);
    /// ```
    pub fn new(value: A, log: W) -> Self {
        Writer {
            run_writer: FnType::new(move |_| (value.clone(), log.clone())),
        }
    }

    /// Creates a `Writer` that only produces a log entry without a value.
    ///
    /// This function is used to add a log entry to the `Writer` monad without
    /// changing the computed value.
    ///
    /// # Arguments
    ///
    /// * `log` - The log entry to be added.
    ///
    /// # Returns
    ///
    /// A new `Writer` instance with the given log and `()` as the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let writer = Writer::<Vec<String>, ()>::tell(vec!["Log entry".to_string()]);
    /// let (value, log) = writer.run();
    ///
    /// assert_eq!(value, ());
    /// assert_eq!(log, vec!["Log entry".to_string()]);
    /// ```
    pub fn tell(log: W) -> Writer<W, ()> {
        Writer::new((), log)
    }

    /// Executes the writer computation and returns the result value along with the accumulated log.
    ///
    /// # Returns
    ///
    /// A tuple containing the computed value of type `A` and the accumulated log of type `W`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let writer = Writer::new(42, vec!["Log entry".to_string()]);
    /// let (value, log) = writer.run();
    ///
    /// assert_eq!(value, 42);
    /// assert_eq!(log, vec!["Log entry".to_string()]);
    /// ```
    pub fn run(&self) -> (A, W) {
        self.run_writer.call(())
    }

    /// Returns the value stored in the `Writer` without the log.
    ///
    /// This method executes the writer computation and returns only the result value,
    /// discarding the accumulated log.
    ///
    /// # Returns
    ///
    /// The computed value of type `A`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let writer = Writer::new(42, vec!["Log entry".to_string()]);
    /// let value = writer.value();
    ///
    /// assert_eq!(value, 42);
    /// ```
    pub fn value(&self) -> A {
        self.run().0
    }

    /// Returns the log stored in the `Writer` without the value.
    ///
    /// This method executes the writer computation and returns only the accumulated log,
    /// discarding the computed value.
    ///
    /// # Returns
    ///
    /// The accumulated log of type `W`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::writer::Writer;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let writer = Writer::new(42, vec!["Log entry".to_string()]);
    /// let log = writer.log();
    ///
    /// assert_eq!(log, vec!["Log entry".to_string()]);
    /// ```
    pub fn log(&self) -> W {
        self.run().1
    }
}

impl<W, A> HKT for Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    type Output<T> = Writer<W, T> where T: TypeConstraints;
}

impl<W, A> Pure<A> for Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        Writer::new(value, W::empty())
    }
}

impl<W, A> Functor<A> for Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w) = self.run();
                (f.call(a), w)
            }),
        }
    }
}

impl<W, A> Applicative<A> for Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (f, w1) = mf.run();
                let (a, w2) = self.run();
                (f.call(a), w1.combine(w2))
            }),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                (f.call((a, b)), w1.combine(w2))
            }),
        }
    }

    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                let (c, w3) = mc.run();
                (f.call((a, b, c)), w1.combine(w2).combine(w3))
            }),
        }
    }
}

impl<W, A> Monad<A> for Writer<W, A>
where
    W: TypeConstraints + Monoid,
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = f.call(a).run();
                (b, w1.combine(w2))
            }),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(|x: A| x.into()))
    }
}

impl<W: TypeConstraints + Monoid, A: TypeConstraints> Identity for Writer<W, A> {}

impl<W: TypeConstraints + Monoid, A: TypeConstraints> Composable for Writer<W, A> {}

impl<W: TypeConstraints + Monoid, A: TypeConstraints> Category for Writer<W, A> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<W: Monoid + TypeConstraints, A: TypeConstraints> Arrow for Writer<W, A> {}