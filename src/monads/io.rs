use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::composable::Composable;
use crate::category::evaluate::Evaluate;
use crate::category::identity::Identity;
use crate::category::monoid::Monoid;
use crate::category::pure::Pure;
use crate::category::semigroup::Semigroup;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::fntype::{FnType, FnTrait};

/// The IO monad.
/// 
/// Represents a computation that performs I/O operations in a functional way.
/// The `IO` monad allows you to sequence operations that interact with the outside world,
/// while maintaining a pure functional interface.
/// 
/// # Generic Arguments
/// * `A` - The type of the output value produced by the computation.
/// 
/// # Laws
/// An `IO` monad must satisfy these laws in addition to the standard Monad laws:
/// 1. Referential Transparency: For any IO computation `io`,
///    `io.run()` must produce the same effect sequence each time
/// 2. Sequential Composition: For IO computations `f` and `g`,
///    `f.bind(g)` must execute `f` before `g`
/// 3. Effect Encapsulation: Side effects must only occur when `run()` is called,
///    not during IO construction or transformation
/// 4. Pure Transformation: For pure function `f` and IO computation `io`,
///    `io.fmap(f)` must not introduce additional side effects
/// 
/// # Fields
/// * `run` - A function that performs the I/O operation.
/// 
/// # Methods
/// * `new` - Creates a new I/O computation from a given function.
/// * `run` - Executes the I/O computation and returns the result.
/// 
/// # Typeclass Implementations
/// The `IO` monad implements the following typeclasses:
/// * `HKT` - Higher-Kinded Types.
/// * `Pure` - For embedding pure values in the monad.
/// * `Functor` - For mapping functions over the result.
/// * `Applicative` - For applying functions within the context.
/// * `Monad` - For chaining computations.
/// * `Composable` - For composing functions.
/// * `Evaluate` - For evaluating the computation.
/// * `Identity` - For creating identity computations.
/// * `Semigroup` - For combining computations.
/// * `Monoid` - For creating empty computations.
/// * `Category` - For creating morphisms.
/// * `Arrow` - For creating arrows.
/// 
/// # Examples
/// Basic usage:
/// ```
/// use rustica::prelude::*;
/// use rustica::monads::io::*;
/// 
/// fn main() {
///     let io_computation = IO::new(FnType::new(|_| "Hello, World!"));
///     let result = io_computation.run();
///     println!("{}", result);
/// }
/// ```
/// 
/// Sequencing computations:
/// ```
/// use rustica::prelude::*;
/// use rustica::monads::io::*;
/// 
/// fn main() {
///     let computation1 = IO::new(FnType::new(|_| "Hello"));
///     let computation2 = IO::new(FnType::new(|_| "World"));
///     let combined = computation1.bind(FnType::new(move |hello| {
///         let computation2_clone = computation2.clone();
///         computation2_clone.fmap(FnType::new(move |world| {
///             format!("{}, {}!", hello, world)
///         }))
///     }));
///     let result = combined.run();
///     println!("{}", result);
/// }
/// ```
/// 
/// File IO:
/// ```
/// use std::fs::File;
/// use std::io::{self, Read, Write};
/// use rustica::prelude::*;
/// use rustica::monads::io::*;
/// 
/// fn main() -> io::Result<()> {
///     let read_file = IO::new(FnType::new(|_| {
///         let mut file = match File::open("input.txt") {
///             Ok(file) => file,
///             Err(err) => {
///                 eprintln!("Error opening file: {}", err);
///                 return String::new();
///             }
///         };
///         let mut contents = String::new();
///         file.read_to_string(&mut contents).unwrap();
///         contents
///     }));
///
///     let write_file = FnType::new(move |contents: String| {
///         let mut file = match File::create("output.txt") {
///             Ok(file) => file,
///             Err(err) => {
///                 eprintln!("Error creating file: {}", err);
///                 return;
///             }
///         };
///         file.write_all(contents.as_bytes()).unwrap();
///     });
///
///     let combined = read_file.bind(FnType::new(move |contents| {
///         let modified_contents = format!("Modified: {}", contents);
///         let write_file_exec = write_file.clone();
///         IO::new(FnType::new(move |_| {
///             write_file_exec.call(modified_contents.clone());
///             ()
///         }))
///     }));
///
///     combined.run();
///     Ok(())
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Function representing the I/O computation.
    pub run: FnType<(), A>,
}

impl<A> IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new IO computation.
    /// 
    /// # Arguments
    /// * `f` - The function to be called.
    /// 
    /// # Returns
    /// * `Self` - The new IO computation.
    pub fn new(f: FnType<(), A>) -> Self
    {
        IO { run: f }
    }

    /// Runs the IO computation.
    /// 
    /// # Returns
    /// * `A` - The result of the computation.
    pub fn run(&self) -> A {
        self.clone().evaluate()
    }
}

impl<A> HKT for IO<A>
where
    A: ReturnTypeConstraints,
{
    type Output<T> = IO<T> where T: ReturnTypeConstraints;
}

impl<A> Pure<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new IO computation that produces a pure value.
    /// 
    /// # Arguments
    /// * `value` - The value to be produced.
    /// 
    /// # Returns
    /// IO<A> - The new IO computation.
    fn pure(value: A) -> Self::Output<A> {
        Self::new(FnType::new(move |_s| value.clone()))
    }
}

impl<A> Functor<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Applies a function to the result of the IO computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// IO<B> - The mapped IO computation.
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        let f = FnType::new(move |_s| f.call(self.run()));
        IO { run: f }
    }
}

impl<A> Applicative<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Applies a function wrapped in an IO computation to the result of another IO computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    /// * `F` - The function to apply.
    /// 
    /// Returns
    /// * `IO<B>` - The applied value.
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(FnType::new(move |a| f.run.call(()).call(a)))
    }

    /// Lifts a binary function into IO computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `F` - The function to lift.
    ///
    /// Returns
    /// * `IO<C>` - The lifted value.
    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        let f = FnType::new(move |_| {
            let (a, b) = (self.run.call(()), mb.run.call(()));
            f.call((a, b))
        });
        IO { run: f }
    }

    /// Lifts a ternary function into IO computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `D` - The type of the third argument.
    /// * `F` - The function to lift.
    ///
    /// Returns
    /// * `IO<D>` - The lifted value.
    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
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
    A: ReturnTypeConstraints,
{
    /// Chains two IO computations together.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the second argument.
    /// * `F` - The function to bind.
    ///
    /// Returns
    /// * `IO<B>` - The chained value.
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        let f = FnType::new(move |_s| f.call(self.run.call(())).run.call(()));
        IO { run: f }
    }

    /// Flattens nested IO computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    ///
    /// Returns
    /// * `IO<B>` - The flattened value.
    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(move |x: A| x.into()))
    }

    /// Composes two monadic functions.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first monadic function.
    /// * `H` - The type of the second monadic function.
    /// 
    /// Returns
    /// * `FnType<A, Self::Output<C>>` - The new computation.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<A> Composable for IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Composes two functions.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the first argument.
    /// * `U` - The type of the second argument.
    /// * `V` - The type of the third argument.
    /// * `F` - The first function.
    /// * `G` - The second function.
    /// 
    /// Returns
    /// * `FnType<T, V>` - The new computation.
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x: T| {
            let u: U = f.call(x);
            g.call(u)
        })
    }
}

impl<A> Evaluate<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Evaluates the IO computation and returns the result.
    /// 
    /// # Type Parameters
    /// * `A` - The type of the argument.
    /// 
    /// Returns
    /// * `A` - The result of the computation.
    fn evaluate(self) -> A {
        self.run.call(())
    }
}

impl<A> Identity for IO<A>
where
    A: ReturnTypeConstraints,
{}

impl<A> Semigroup for IO<A>
where
    A: Semigroup + ReturnTypeConstraints,
{
    /// Combines two IO computations.
    /// 
    /// # Type Parameters
    /// * `A` - The type of the argument.
    /// 
    /// Returns
    /// * `IO<A>` - The combined computation.
    fn combine(self, other: Self) -> Self {
        let f = FnType::new(move |_s| self.run.call(()).combine(other.run.call(())));
        IO { run: f }
    }
}

impl<A> Monoid for IO<A>
where
    A: Monoid + ReturnTypeConstraints,
{
    /// Creates an empty IO computation.
    /// 
    /// Returns
    /// * `IO<A>` - The empty computation.
    fn empty() -> Self {
        IO::new(FnType::new(|_| A::empty()))
    }
}

impl<A> Category for IO<A>
where
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        FnType::new(|x| x)
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
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<A> Arrow for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        FnType::new(move |x| f.call(x))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        FnType::new(move |(b, d)| (f.call(b), d))
    }
}
