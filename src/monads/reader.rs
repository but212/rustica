use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::identity::Identity;
use crate::category::composable::Composable;
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

impl<E, A> Identity for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<E, A> Composable for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |t| g.call(f.call(t)))
    }
}

impl<E, A> Category<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = Reader<E, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        Reader {
            run: FnType::new(|_| B::default())
        }
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        Reader {
            run: FnType::new(move |e: E| {
                let _ = f.run_reader(e.clone());
                g.run_reader(e)
            })
        }
    }
}

impl<E, A> Arrow<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        Reader {
            run: FnType::new(move |_| f.call(B::default()))
        }
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        Reader {
            run: FnType::new(move |e| {
                let c = f.run_reader(e);
                (c, D::default())
            })
        }
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
    fn pure(value: A) -> Self::Output<A> {
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
        Reader::new(FnType::new(move |e| f.call(self.run_reader(e))))
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
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            mf.run_reader(e).call(self.run_reader(e1))
        }))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            f.call(self.run_reader(e)).call(mb.run_reader(e1))
        }))
    }

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
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            let e2 = e.clone();
            f.call(self.run_reader(e))
                .call(mb.run_reader(e1))
                .call(mc.run_reader(e2))
        }))
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
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            f.call(self.run_reader(e)).run_reader(e1)
        }))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        A: ReturnTypeConstraints,
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            self.run_reader(e).into().run_reader(e1)
        }))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |a| {
            g.call(a).bind(h.clone())
        })
    }
}

/// Helper functions for Reader
impl<E, A> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Gets the environment from a Reader.
    pub fn ask() -> Reader<E, E> {
        Reader::new(FnType::new(|e| e))
    }

    /// Gets a function of the environment from a Reader.
    pub fn asks<F>(f: F) -> Reader<E, A>
    where
        F: FnTrait<E, A>,
    {
        Reader::new(f)
    }

    /// Modifies the environment before running a Reader.
    pub fn local<F>(f: F, reader: Reader<E, A>) -> Reader<E, A>
    where
        F: FnTrait<E, E>,
    {
        Reader::new(FnType::new(move |e| reader.run_reader(f.call(e))))
    }
}
