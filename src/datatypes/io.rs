use std::fmt;
use std::sync::Arc;
use crate::traits::hkt::{HKT, TypeOps, AnyBox};
use crate::traits::functor::Functor;
use crate::traits::identity::Identity;
use crate::traits::pure::Pure;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;

/// The IO monad.
///
/// Represents an IO operation that, when executed, will perform a side effect and return a value of type `A`.
///
/// # Type Parameters
///
/// * `A`: The type of value returned by the IO operation. It must implement `TypeOps`, `Clone`, `Default`, `Send`, `Sync`, `PartialEq`, and have a `'static` lifetime.
///
/// # Fields
///
/// * `run`: An `Arc`-wrapped function that represents the IO operation. When called, it returns a value of type `A`.
///
/// # Examples
///
/// ```
/// use std::sync::Arc;
/// use rustica::datatypes::io::IO;
///
/// // Create an IO that prints to console and returns a string
/// let io = IO::new(Arc::new(|| {
///     println!("Hello, world!");
///     "Hello".to_string()
/// }));
///
/// // Run the IO operation
/// let result = io.run();
/// assert_eq!(result, "Hello");
/// ```
pub struct IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    /// The underlying function representing the IO operation.
    pub run: Arc<dyn Fn() -> A + Send + Sync>,
}

impl<A> IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    /// Creates a new `IO` instance.
    ///
    /// # Parameters
    ///
    /// * `f`: An `Arc`-wrapped function that represents the IO operation.
    ///
    /// # Returns
    ///
    /// A new `IO` instance encapsulating the provided function.
    pub fn new(f: Arc<dyn Fn() -> A + Send + Sync>) -> Self {
        IO { run: f }
    }

    /// Executes the IO operation and returns the result.
    ///
    /// # Returns
    ///
    /// The result of type `A` produced by executing the encapsulated IO operation.
    pub fn run(&self) -> A {
        (self.run)()
    }
}

impl<A> Clone for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn clone(&self) -> Self {
        IO { run: Arc::clone(&self.run) }
    }
}

impl<A> fmt::Debug for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IO")
            .field("run", &"<function>")
            .finish()
    }
}

impl<A> Default for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn default() -> Self {
        IO::new(Arc::new(|| A::default()))
    }
}


impl<A> HKT for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn apply_type(&self) -> AnyBox {
        self.clone_box()
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<IO<A>>().map(|x| x.clone_box())
    }
}

impl<A> TypeOps for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn equals(&self, other: &AnyBox) -> bool {
        if let Some(other_io) = other.downcast_ref::<IO<A>>() {
            let self_val = (self.run)();
            let other_val = (other_io.run)();
            self_val == other_val
        } else {
            false
        }
    }
}

impl<A> Pure for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn pure(value: AnyBox) -> AnyBox {
        let val = value.downcast_ref::<A>()
            .map(|v| v.clone())
            .unwrap_or_else(A::default);
        Arc::new(IO::new(Arc::new(move || val.clone()))) as AnyBox
    }
}

impl<A> Identity for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn identity() -> AnyBox {
        Arc::new(IO::new(Arc::new(|| A::default()))) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<A> Functor for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync + 'static>) -> AnyBox {
        let io_run = Arc::clone(&self.run);
        Arc::new(IO::new(Arc::new(move || {
            let value = io_run();
            let boxed_value = Arc::new(value) as AnyBox;
            if let Some(result) = f(boxed_value).downcast_ref::<A>() {
                result.clone()
            } else {
                A::default()
            }
        }))) as AnyBox
    }
}

impl<A> Applicative for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let io = self.clone();
        Arc::new(IO::new(Arc::new(move || {
            let result = io.run();
            let result_box = Arc::new(result) as AnyBox;
            let f_result = f(result_box);
            if let Some(a) = f_result.downcast_ref::<A>() {
                a.clone()
            } else {
                A::default()
            }
        }))) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(io_b) = b.downcast_ref::<IO<A>>() {
            let io_a = self.clone();
            let io_b = io_b.clone();
            Arc::new(IO::new(Arc::new(move || {
                let a = io_a.run();
                let b = io_b.run();
                let boxed_a = Arc::new(a) as AnyBox;
                let boxed_b = Arc::new(b) as AnyBox;
                if let Some(result) = f(boxed_a, boxed_b).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }))) as AnyBox
        } else {
            Arc::new(IO::<A>::default()) as AnyBox
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(io_b), Some(io_c)) = (b.downcast_ref::<IO<A>>(), c.downcast_ref::<IO<A>>()) {
            let io_a = self.clone();
            let io_b = io_b.clone();
            let io_c = io_c.clone();
            Arc::new(IO::new(Arc::new(move || {
                let a = io_a.run();
                let b = io_b.run();
                let c = io_c.run();
                let boxed_a = Arc::new(a) as AnyBox;
                let boxed_b = Arc::new(b) as AnyBox;
                let boxed_c = Arc::new(c) as AnyBox;
                if let Some(result) = f(boxed_a, boxed_b, boxed_c).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }))) as AnyBox
        } else {
            Arc::new(IO::<A>::default()) as AnyBox
        }
    }
}

impl<A> Arrow for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let f = Arc::clone(func);
            Arc::new(IO::<A>::new(Arc::new(move || {
                let default_value = A::default();
                let boxed_value = Arc::new(default_value) as AnyBox;
                if let Some(result) = f(boxed_value).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }))) as AnyBox
        } else {
            Arc::new(IO::<A>::default()) as AnyBox
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let io_run = Arc::clone(&self.run);
            let f = Arc::clone(func);
            Arc::new(IO::<A>::new(Arc::new(move || {
                let value = io_run();
                let boxed_value = Arc::new(value) as AnyBox;
                if let Some(result) = f(boxed_value).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }))) as AnyBox
        } else {
            Arc::new(IO::<A>::default()) as AnyBox
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        self.first(f)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        if let (Some(f), Some(g)) = (
            f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
            g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
        ) {
            let io_run = Arc::clone(&self.run);
            let f = Arc::clone(f);
            let g = Arc::clone(g);
            Arc::new(IO::<A>::new(Arc::new(move || {
                let value = io_run();
                let boxed_value1 = Arc::new(value.clone()) as AnyBox;
                let boxed_value2 = Arc::new(value) as AnyBox;
                let result1 = f(boxed_value1);
                let result2 = g(boxed_value2);
                if let (Some(r1), Some(_r2)) = (result1.downcast_ref::<A>(), result2.downcast_ref::<A>()) {
                    r1.clone()
                } else {
                    A::default()
                }
            }))) as AnyBox
        } else {
            Arc::new(IO::<A>::default()) as AnyBox
        }
    }
}

impl<A> Monad for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let io_run = Arc::clone(&self.run);
        Arc::new(IO::<A>::new(Arc::new(move || {
            let value = io_run();
            let boxed_value = Arc::new(value) as AnyBox;
            if let Some(io_result) = f(boxed_value).downcast_ref::<IO<A>>() {
                (io_result.run)()
            } else {
                A::default()
            }
        }))) as AnyBox
    }

    fn join(&self) -> AnyBox {
        let io_run = Arc::clone(&self.run);
        Arc::new(IO::<A>::new(Arc::new(move || {
            let inner_io = io_run();
            let boxed_io = Arc::new(inner_io) as AnyBox;
            if let Some(io) = boxed_io.downcast_ref::<IO<A>>() {
                (io.run)()
            } else {
                A::default()
            }
        }))) as AnyBox
    }
}

impl<A> Composable for IO<A>
where
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn compose(
        &self,
        g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        let g = g.clone();
        let f = f.clone();
        Arc::new(move |x: AnyBox| -> AnyBox {
            g(f(x))
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let io_run = Arc::clone(&self.run);
        Arc::new(IO::<A>::new(Arc::new(move || {
            let value = io_run();
            let boxed_value = Arc::new(value) as AnyBox;
            if let Some(result) = f(boxed_value).downcast_ref::<A>() {
                result.clone()
            } else {
                A::default()
            }
        }))) as AnyBox
    }
}
