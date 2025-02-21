use crate::traits::applicative::Applicative;
use crate::traits::arrow::Arrow;
use crate::traits::category::Category;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::fntype::{FnTrait, FnType};

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
/// use rustica::datatypes::reader::Reader;
/// use rustica::fntype::{FnType, FnTrait};
/// 
/// let reader: Reader<i32, String> = Reader::new(FnType::new(|e| format!("Environment: {}", e)));
/// assert_eq!(reader.run_reader(42), "Environment: 42");
/// 
/// let modified = Reader::local(FnType::new(|e: i32| e * 2), reader);
/// assert_eq!(modified.run_reader(21), "Environment: 42");
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Reader<E: TypeConstraints, A: TypeConstraints> {
    /// The function that represents the Reader computation.
    /// It takes an environment of type `E` and produces a result of type `A`.
    run: FnType<E, A>,
}

impl<E: TypeConstraints, A: TypeConstraints> Reader<E, A> {
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
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let reader = Reader::new(FnType::new(|e: i32| e.to_string()));
    /// assert_eq!(reader.run_reader(42), "42");
    /// ```
    pub fn new<F: FnTrait<E, A>>(f: F) -> Self {
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
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let reader = Reader::new(FnType::new(|e: i32| e * 2));
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    pub fn run_reader(&self, e: E) -> A {
        self.run.call(e)
    }
}

impl<E: TypeConstraints, A: TypeConstraints> HKT for Reader<E, A> {
    type Output<T> = Reader<E, T> where T: TypeConstraints;
}

impl<E: TypeConstraints, A: TypeConstraints> Pure<A> for Reader<E, A> {
    fn pure(value: A) -> Self::Output<A> {
        let value = value.clone();
        Reader::new(FnType::new(move |_: E| value.clone()))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Functor<A> for Reader<E, A> {
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e| f.call(self.run_reader(e))))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Applicative<A> for Reader<E, A> {
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e: E| {
            let f = mf.run_reader(e.clone());
            let a = self.run_reader(e);
            f.call(a)
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

impl<E: TypeConstraints, A: TypeConstraints> Monad<A> for Reader<E, A> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let a = self.run_reader(e.clone());
            f.call(a).run_reader(e)
        }))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        Reader::new(FnType::new(move |e: E| {
            let reader_b = self.run_reader(e.clone()).into();
            reader_b.run_reader(e)
        }))
    }

    fn then<B: TypeConstraints>(self, mb: Self::Output<B>) -> Self::Output<B> {
        self.bind(FnType::new(move |_| mb.clone()))
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Reader::new(FnType::new(move |e| f.call(self.run_reader(e))))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Composable<A> for Reader<E, A> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<A, U>,
    {
        Reader::new(FnType::new(move |e| {
            let a = self.run_reader(e);
            f.call(a)
        }))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Identity<A> for Reader<E, A> {
    fn identity() -> Self::Output<A> {
        Reader::new(FnType::new(|_| A::default()))
    }

    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<A, U>,
    {
        Reader::new(FnType::new(move |_| f.call(A::default())))
    }
}

impl<E: TypeConstraints, A: TypeConstraints> Category<A> for Reader<E, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<E: TypeConstraints, A: TypeConstraints> Arrow<A, A> for Reader<E, A> {}

impl<E: TypeConstraints, A: TypeConstraints> Reader<E, A> {
    /// Gets the environment from a Reader.
    /// 
    /// # Examples
    /// ```
    /// use rustica::datatypes::reader::Reader;
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
    /// use rustica::datatypes::reader::Reader;
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
    /// use rustica::datatypes::reader::Reader;
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
