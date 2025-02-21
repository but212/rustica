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
/// impl Semigroup<Log> for Log {
///     fn combine(mut self, other: Self) -> Self {
///         self.0.extend(other.0);
///         self
///     }
/// }
///
/// impl Monoid<Log> for Log {
///     fn empty() -> Self {
///         Log(Vec::new())
///     }
/// }
///
/// let writer = Writer::new(42, Log(vec!["Initial log".to_string()]));
/// let (value, log) = writer.run_writer();
///
/// assert_eq!(value, 42);
/// assert_eq!(log, Log(vec!["Initial log".to_string()]));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Writer<W: TypeConstraints + Monoid<W>, A: TypeConstraints> {
    run_writer: FnType<(), (A, W)>,
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Writer<W, A> {
    /// Creates a new Writer with a value and a log.
    pub fn new(value: A, log: W) -> Self {
        Writer {
            run_writer: FnType::new(move |_| (value.clone(), log.clone())),
        }
    }

    /// Runs the writer computation and returns the value and the log.
    pub fn run_writer(&self) -> (A, W) {
        self.run_writer.call(())
    }

    /// Gets the value from the writer computation.
    pub fn value(&self) -> A {
        self.run_writer().0
    }

    /// Gets the log from the writer computation.
    pub fn log(&self) -> W {
        self.run_writer().1
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Default for Writer<W, A>
where
    A: Default,
{
    fn default() -> Self {
        Writer::new(A::default(), W::empty())
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> HKT for Writer<W, A> {
    type Output<T> = Writer<W, T> where T: TypeConstraints;
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Pure<A> for Writer<W, A> {
    fn pure(x: A) -> Self::Output<A> {
        Writer::new(x, W::empty())
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Functor<A> for Writer<W, A> {
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        let (a, w) = self.run_writer();
        Writer::new(f.call(a), w)
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Applicative<A> for Writer<W, A> {
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        let (a, w1) = self.run_writer();
        let (f, w2) = mf.run_writer();
        Writer::new(f.call(a), w1.combine(w2))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        let (a, w1) = self.run_writer();
        let (b, w2) = mb.run_writer();
        Writer::new(f.call((a, b)), w1.combine(w2))
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
        let (a, w1) = self.run_writer();
        let (b, w2) = mb.run_writer();
        let (c, w3) = mc.run_writer();
        Writer::new(f.call((a, b, c)), w1.combine(w2).combine(w3))
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Monad<A> for Writer<W, A> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        let (a, w1) = self.run_writer();
        let (b, w2) = f.call(a).run_writer();
        Writer::new(b, w1.combine(w2))
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        let (a, w) = self.run_writer();
        Writer::new(f.call(a), w)
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>
    {
        self.run_writer().0.into()
    }

    fn then<B>(self, mb: Self::Output<B>) -> Self::Output<B>
    where
        B: TypeConstraints,
    {
        let (_a, w1) = self.run_writer();
        let (_b, w2) = mb.run_writer();
        Writer::new(_b, w1.combine(w2))
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Composable<A> for Writer<W, A> {
    fn compose_with<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        let (a, w) = self.run_writer();
        Writer::new(f.call(a), w)
    }
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Category<A> for Writer<W, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Arrow<A, A> for Writer<W, A> {}

impl<W: TypeConstraints + Monoid<W>, A: TypeConstraints> Identity<A> for Writer<W, A> {
    fn map_identity<B, F>(f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Writer::new(f.call(A::default()), W::empty())
    }
}