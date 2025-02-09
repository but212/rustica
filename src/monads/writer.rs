use std::fmt::Debug;
use std::sync::Arc;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::monoid::Monoid;
use crate::fntype::{FnType, FnTrait};

/// The writer monad.
/// 
/// # Type Parameters
/// * `W` - The log type, must implement the `Monoid` trait.
/// * `A` - The output type.
/// 
/// # Laws
/// A Writer instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Log Monoid: The log type `W` must satisfy monoid laws:
///    - Identity: `w.combine(W::empty()) = w = W::empty().combine(w)`
///    - Associativity: `(w1.combine(w2)).combine(w3) = w1.combine(w2.combine(w3))`
/// 2. Pure Log Empty: For any value `x`,
///    `Writer::pure(x).log() = W::empty()`
/// 3. Tell Consistency: For any log `w`,
///    `Writer::tell(w).log() = w`
/// 4. Log Combination: For Writers `w1` and `w2`,
///    `w1.bind(w2).log() = w1.log().combine(w2(w1.value()).log())`
/// 5. Value Independence: For any log `w` and value `x`,
///    `Writer::new(x, w).value() = x`
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// The function that runs the writer computation.
    run_writer: FnType<(), (A, W)>,
}

impl<W, A> Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Creates a new Writer from a value and a log.
    /// 
    /// # Arguments
    /// * `value` - The value to be written.
    /// * `log` - The log to be written.
    /// 
    /// # Returns
    /// * `Writer<W, A>` - The new Writer.
    pub fn new(value: A, log: W) -> Self {
        let value = Arc::new(value);
        let log = Arc::new(log);
        Writer {
            run_writer: FnType::new(move |_| ((*value).clone(), (*log).clone())),
        }   
    }

    /// Creates a new Writer that writes a log.
    /// 
    /// # Arguments
    /// * `log` - The log to be written.
    /// 
    /// # Returns
    /// * `Writer<W, ()>` - The new Writer.
    pub fn tell(log: W) -> Writer<W, ()> {
        Writer::new((), log)
    }

    /// Runs the writer computation.
    /// 
    /// # Returns
    /// * `(A, W)` - The value and log.
    pub fn run(&self) -> (A, W) {
        self.run_writer.call(())
    }

    /// Gets the value.
    /// 
    /// # Returns
    /// * `A` - The value.
    pub fn value(&self) -> A {
        self.run().0
    }

    /// Gets the log.
    /// 
    /// # Returns
    /// * `W` - The log.
    pub fn log(&self) -> W {
        self.run().1
    }
}

impl<W, A> HKT for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    type Output<T> = Writer<W, T> where T: ReturnTypeConstraints;
}

impl<W, A> Pure<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Creates a new Writer that writes a value.
    /// 
    /// # Arguments
    /// * `value` - The value to be written.
    /// 
    /// # Returns
    /// * `Writer<W, A>` - The new Writer.
    fn pure(value: A) -> Self::Output<A> {
        Writer::new(value, W::empty())
    }
}

impl<W, A> Functor<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Maps a function over the value.
    /// 
    /// # Arguments
    /// * `f` - The function to be mapped.
    /// 
    /// # Returns
    /// * `Writer<W, B>` - The new Writer.
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
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
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Applies a function to a value.
    /// 
    /// # Arguments
    /// * `mf` - The function to be applied.
    /// 
    /// # Returns
    /// * `Writer<W, B>` - The new Writer.
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
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

    /// Lifts a binary function into Writer computations.
    /// 
    /// # Arguments
    /// * `mb` - The second argument to the function.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `Writer<W, C>` - The new Writer.
    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                (f.call(a).call(b), w1.combine(w2))
            }),
        }
    }

    /// Lifts a ternary function into Writer computations.
    /// 
    /// # Arguments
    /// * `mb` - The second argument to the function.
    /// * `mc` - The third argument to the function.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `Writer<W, D>` - The new Writer.
    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
    {
        Writer {
            run_writer: FnType::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                let (c, w3) = mc.run();
                (f.call(a).call(b).call(c), w1.combine(w2).combine(w3))
            }),
        }
    }
}

impl<W, A> Monad<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Binds a function over the value.
    /// 
    /// # Arguments
    /// * `f` - The function to be bound.
    /// 
    /// # Returns
    /// * `Writer<W, B>` - The new Writer.
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
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

    /// Joins a Writer computation by returning the inner value.
    /// 
    /// # Returns
    /// * `Writer<W, A>` - The inner value.
    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(|x: A| x.into()))
    }

    /// Composes two monadic functions.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first monadic function.
    /// * `H` - The type of the second monadic function.
    /// 
    /// # Returns
    /// * `FnType<A, Self::Output<C>>` - The new computation.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x: A| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}