use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::composable::Composable;
use crate::traits::evaluate::Evaluate;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::fntype::{FnType, FnTrait};

/// The IO monad.
///
/// Represents an IO operation that, when executed, will perform a side effect and return a value of type `A`.
///
/// # Type Parameters
///
/// * `A`: The type of the value returned by the IO operation. Must implement `TypeConstraints`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use rustica::prelude::*;
/// use rustica::datatypes::io::IO;
///
/// let io = IO::new(FnType::new(|_| println!("Hello, world!")));
/// io.run(); // Prints "Hello, world!"
/// ```
///
/// Chaining IO operations:
///
/// ```
/// use rustica::prelude::*;
/// use rustica::datatypes::io::IO;
///
/// let io1 = IO::new(FnType::new(|_| 42));
/// let io2 = io1.fmap(FnType::new(|x| x * 2));
/// assert_eq!(io2.run(), 84);
/// ```
///
/// File IO:
/// ```
/// use std::fs::File;
/// use std::io::{self, Read, Write};
/// use rustica::prelude::*;
/// use rustica::datatypes::io::IO;
///
/// fn read_file() -> IO<String> {
///     IO::new(FnType::new(|_| {
///         let mut file = match File::open("input.txt") {
///             Ok(file) => file,
///             Err(err) => {
///                 eprintln!("Error opening file: {}", err);
///                 return String::new();
///             }
///         };
///         let mut contents = String::new();
///         if let Err(err) = file.read_to_string(&mut contents) {
///             eprintln!("Error reading file: {}", err);
///             return String::new();
///         }
///         contents
///     }))
/// }
///
/// fn write_file(contents: String) -> IO<()> {
///     IO::new(FnType::new(move |_| {
///         let mut file = File::create("output.txt").expect("Failed to create file");
///         file.write_all(contents.as_bytes()).expect("Failed to write to file");
///     }))
/// }
///
/// fn main() -> io::Result<()> {
///     let program = read_file().bind(FnType::new(|contents| {
///         let modified = format!("Modified: {}", contents);
///         write_file(modified)
///     }));
///
///     program.run();
///     Ok(())
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct IO<A>
where
    A: TypeConstraints,
{
    /// The underlying function representing the IO operation.
    pub run: FnType<(), A>,
}

impl<A> IO<A>
where
    A: TypeConstraints,
{
    /// Creates a new `IO` instance.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes no arguments and returns a value of type `A`.
    ///
    /// # Returns
    ///
    /// A new `IO` instance wrapping the provided function.
    pub fn new(f: FnType<(), A>) -> Self {
        IO { run: f }
    }

    /// Executes the IO operation and returns the result.
    ///
    /// This method runs the underlying function and produces the value of type `A`.
    ///
    /// # Returns
    ///
    /// The result of the IO operation of type `A`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::io::IO;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let io = IO::new(FnType::new(|_| 42));
    /// assert_eq!(io.run(), 42);
    /// ```
    pub fn run(&self) -> A {
        self.clone().evaluate()
    }
}

impl<A> HKT for IO<A>
where
    A: TypeConstraints,
{
    type Output<T> = IO<T> where T: TypeConstraints;
}

impl<A> Pure<A> for IO<A>
where
    A: TypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        Self::new(FnType::new(move |_s| value.clone()))
    }
}

impl<A> Functor<A> for IO<A>
where
    A: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        let f = FnType::new(move |_s| f.call(self.run()));
        IO { run: f }
    }
}

impl<A> Applicative<A> for IO<A>
where
    A: TypeConstraints,
{
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(FnType::new(move |a| f.run.call(()).call(a)))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        let f = FnType::new(move |_| {
            let (a, b) = (self.run.call(()), mb.run.call(()));
            f.call((a, b))
        });
        IO { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        let f = FnType::new(move |_| {
            let (a, b, c) = (self.run.call(()), mb.run.call(()), mc.run.call(()));
            f.call((a, b, c))
        });
        IO { run: f }
    }
}

impl<A> Monad<A> for IO<A>
where
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        let f = FnType::new(move |_s| f.call(self.run.call(())).run.call(()));
        IO { run: f }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(move |x: A| x.into()))
    }
}

impl<A: TypeConstraints> Composable for IO<A> {}

impl<A: TypeConstraints> Evaluate<A> for IO<A> {
    fn evaluate(self) -> A {
        self.run.call(())
    }
}

impl<A: TypeConstraints> Identity for IO<A> {}

impl<A: TypeConstraints> Semigroup for IO<A>
where
    A: Semigroup + TypeConstraints,
{
    fn combine(self, other: Self) -> Self {
        let f = FnType::new(move |_s| self.run.call(()).combine(other.run.call(())));
        IO { run: f }
    }
}

impl<A> Monoid for IO<A>
where
    A: Monoid + TypeConstraints,
{
    fn empty() -> Self {
        IO::new(FnType::new(|_| A::empty()))
    }
}

impl<A: TypeConstraints> Category for IO<A>
where
    A: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<A: TypeConstraints> Arrow for IO<A> {}
