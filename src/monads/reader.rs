use crate::category::hkt::{HKT, TypeConstraints};
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
/// 1. Environment Access: For any environment `e`, `ask().run_reader(e) = e`
/// 2. Environment Modification: For function `f` and Reader `r`, `local(f, r).run_reader(e) = r.run_reader(f(e))`
/// 3. Environment Consistency: For Readers `r1` and `r2`, `r1.bind(r2).run_reader(e) = r2(r1.run_reader(e)).run_reader(e)`
/// 4. Pure Environment Independence: For any value `x` and environment `e`, `Reader::pure(x).run_reader(e) = x`
/// 5. Local Identity: For any Reader `r`, `local(|x| x, r) = r`
/// 6. Local Composition: For functions `f`, `g` and Reader `r`, `local(f, local(g, r)) = local(|e| g(f(e)), r)`
/// 
/// # Examples
/// ```
/// use rustica::monads::reader::Reader;
/// use rustica::fntype::{FnType, FnTrait};
/// 
/// let reader: Reader<i32, String> = Reader::new(FnType::new(|e| format!("Environment: {}", e)));
/// assert_eq!(reader.run_reader(42), "Environment: 42");
/// 
/// let modified = Reader::local(FnType::new(|e: i32| e * 2), reader);
/// assert_eq!(modified.run_reader(21), "Environment: 42");
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    /// The function that represents the Reader computation.
    /// It takes an environment of type `E` and produces a result of type `A`.
    run: FnType<E, A>,
}

impl<E, A> Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    /// Creates a new `Reader` instance.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes an environment of type `E` and returns a value of type `A`.
    ///
    /// # Returns
    ///
    /// A new `Reader` instance wrapping the provided function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let reader = Reader::new(FnType::new(|e: i32| e.to_string()));
    /// assert_eq!(reader.run_reader(42), "42");
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<E, A>,
    {
        Reader {
            run: FnType::new(move |e| f.call(e)),
        }
    }

    /// Runs the Reader computation with the given environment.
    ///
    /// # Arguments
    ///
    /// * `e` - The environment of type `E` to run the Reader with.
    ///
    /// # Returns
    ///
    /// The result of type `A` after applying the Reader's function to the environment.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let reader = Reader::new(FnType::new(|e: i32| e * 2));
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    pub fn run_reader(&self, e: E) -> A {
        self.run.call(e)
    }
}

impl<E, A> HKT for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    type Output<T> = Reader<E, T> where T: TypeConstraints;
}

impl<E, A> Pure<A> for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        let value = value.clone();
        Reader::new(FnType::new(move |_: E| value.clone()))
    }
}

impl<E, A> Functor<A> for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e| f.call(self.run_reader(e))))
    }
}

impl<E, A> Applicative<A> for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            mf.run_reader(e).call(self.run_reader(e1))
        }))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            f.call((self.run_reader(e), mb.run_reader(e1)))
        }))
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
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            let e2 = e.clone();
            f.call((self.run_reader(e), mb.run_reader(e1), mc.run_reader(e2)))
        }))
    }
}

impl<E, A> Monad<A> for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            f.call(self.run_reader(e)).run_reader(e1)
        }))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        A: TypeConstraints,
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let e1 = e.clone();
            self.run_reader(e).into().run_reader(e1)
        }))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |a| {
            g.call(a).bind(h.clone())
        })
    }
}

impl<E, A> Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    /// Gets the environment from a Reader.
    /// 
    /// # Examples
    /// ```
    /// use rustica::monads::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    /// 
    /// let reader: Reader<i32, i32> = Reader::<i32, i32>::ask();
    /// assert_eq!(reader.run_reader(42), 42);
    /// ```
    pub fn ask() -> Reader<E, E> {
        Reader::new(FnType::new(|e| e))
    }

    /// Gets a function of the environment from a Reader.
    /// 
    /// # Examples
    /// ```
    /// use rustica::monads::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    /// 
    /// let reader = Reader::asks(FnType::new(|e: i32| e * 2));
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    pub fn asks<F>(f: F) -> Reader<E, A>
    where
        F: FnTrait<E, A>,
    {
        Reader::new(f)
    }

    /// Modifies the environment before running a Reader.
    /// 
    /// # Examples
    /// ```
    /// use rustica::monads::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    /// 
    /// let reader = Reader::new(FnType::new(|e: i32| e.to_string()));
    /// let modified = Reader::local(FnType::new(|e: i32| e * 2), reader);
    /// assert_eq!(modified.run_reader(21), "42");
    /// ```
    pub fn local<F>(f: F, reader: Reader<E, A>) -> Reader<E, A>
    where
        F: FnTrait<E, E>,
    {
        Reader::new(FnType::new(move |e| reader.run_reader(f.call(e))))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Identity for Reader<E, A> {}

impl<E: TypeConstraints, A: TypeConstraints> Composable for Reader<E, A> {}

impl<E: TypeConstraints, A: TypeConstraints> Category for Reader<E, A>
where
    E: TypeConstraints,
    A: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<E: TypeConstraints, A: TypeConstraints> Arrow for Reader<E, A> {}
