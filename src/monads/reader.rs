use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::fntype::{FnType, FnTrait};

/// A Reader monad that represents a computation with access to an environment.
/// 
/// # Type Parameters
/// * `E` - The environment type.
/// * `A` - The output type.
/// 
/// # Laws
/// A Reader instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Environment Access: For any environment `e`,
///    `ask().run_reader(e) = e`
/// 2. Environment Modification: For function `f` and Reader `r`,
///    `local(f, r).run_reader(e) = r.run_reader(f(e))`
/// 3. Environment Consistency: For Readers `r1` and `r2`,
///    `r1.bind(r2).run_reader(e) = r2(r1.run_reader(e)).run_reader(e)`
/// 4. Pure Environment Independence: For any value `x` and environment `e`,
///    `Reader::pure(x).run_reader(e) = x`
/// 5. Local Identity: For any Reader `r`,
///    `local(|x| x, r) = r`
/// 6. Local Composition: For functions `f`, `g` and Reader `r`,
///    `local(f, local(g, r)) = local(|e| g(f(e)), r)`
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The function that reads from the environment.
    run: FnType<E, A>,
}

impl<E, A> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new reader computation.
    /// 
    /// # Arguments
    /// * `f` - The function to be called.
    ///
    /// # Returns
    /// * `Reader<E, A>` - The reader computation.
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<E, A>,
    {
        Reader {
            run: FnType::new(move |e| f.call(e)),
        }
    }

    /// Runs the reader computation with the given environment.
    /// 
    /// # Arguments
    /// * `e` - The environment to run the reader computation with.
    /// 
    /// # Returns
    /// * `A` - The result of the reader computation.
    pub fn run_reader(&self, e: E) -> A {
        self.run.call(e)
    }
}

impl<E, A> HKT for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Reader<E, T> where T: ReturnTypeConstraints;
}

impl<E, A> Pure<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A>
    {
        let value = value.clone();
        Reader::new(FnType::new(move |_: E| value.clone()))
    }
}

impl<E, A> Functor<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        let f = FnType::new(move |e: E| f.call(self.run_reader(e)));
        Reader { run: f }
    }
}

impl<E, A> Applicative<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B> + Default,
    {
        let f = FnType::new(move |e: E| {
            let f = mf.run_reader(e.clone());
            f.call(self.run_reader(e))
        });
        Reader { run: f }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
    {
        let f = FnType::new(move |e: E| {
            let a = self.run_reader(e.clone());
            let b = mb.run_reader(e);
            f.call(a).call(b)
        });
        Reader { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
    {
        let f = FnType::new(move |e: E| {
            let a = self.run_reader(e.clone());
            let b = mb.run_reader(e.clone());
            let c = mc.run_reader(e);
            f.call(a).call(b).call(c)
        });
        Reader { run: f }
    }
}

impl<E, A> Monad<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        let f = FnType::new(move |e: E| {
            let a = self.run_reader(e.clone());
            f.call(a).run_reader(e)
        });
        Reader { run: f }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(|x: A| x.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>> + Clone,
        H: FnTrait<B, Self::Output<C>> + Clone,
    {
        FnType::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

/// Gets the environment from a Reader.
pub fn ask<E>() -> Reader<E, E>
where
    E: ReturnTypeConstraints,
{
    Reader::new(FnType::new(|e: E| e))
}

/// Gets a function of the environment from a Reader.
pub fn asks<E, A, F>(f: F) -> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    F: FnTrait<E, A>,
{
    Reader::new(f)
}

/// Modifies the environment before running a Reader.
pub fn local<E, A, F>(f: F, reader: Reader<E, A>) -> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    F: FnTrait<E, E>,
{
    let f = FnType::new(move |e: E| reader.run_reader(f.call(e)));
    Reader { run: f }
}
