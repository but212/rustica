use std::sync::Arc;
use std::any::Any;
use crate::traits::{
    functor::Functor,
    applicative::Applicative,
    monad::Monad,
    pure::Pure,
    hkt::*,
    identity::Identity,
    category::Category,
};

/// A Reader monad that represents a computation with access to an environment.
/// 
/// The Reader monad allows you to perform computations that depend on some environment `E`.
/// It's particularly useful for dependency injection and managing configurations.
/// 
/// # Type Parameters
/// 
/// * `E`: The type of the environment.
/// 
/// # Examples
/// 
/// Basic usage:
/// ```
/// use rustica::datatypes::reader::Reader;
/// 
/// // Create a Reader that formats the environment
/// let reader: Reader<i32> = Reader::new(|e: &i32| format!("Environment: {}", e));
/// 
/// // Run the Reader with an environment
/// let result = reader.run_reader(&42);
/// assert_eq!(*result.downcast_ref::<String>().unwrap(), "Environment: 42");
/// 
/// // Modify the environment before running
/// let modified: Reader<i32> = Reader::local(|e: &i32| e * 2, reader);
/// let result = modified.run_reader(&21);
/// assert_eq!(*result.downcast_ref::<String>().unwrap(), "Environment: 42");
/// 
/// // Get the environment itself
/// let ask_reader: Reader<String> = Reader::ask();
/// let result = ask_reader.run_reader(&"Hello".to_string());
/// assert_eq!(*result.downcast_ref::<String>().unwrap(), "Hello");
/// 
/// // Apply a function to the environment
/// let asks_reader: Reader<Vec<i32>> = Reader::asks(|v: &Vec<i32>| v.len());
/// let result = asks_reader.run_reader(&vec![1, 2, 3]);
/// assert_eq!(*result.downcast_ref::<usize>().unwrap(), 3);
/// ```
#[derive(Clone)]
pub struct Reader<E> {
    /// The function that represents the Reader computation.
    /// It takes a reference to an environment and produces a type-erased result.
    run: Arc<dyn for<'a> Fn(&'a E) -> Arc<dyn Any + Send + Sync> + Send + Sync>,
}

impl<E> Reader<E>
where
    E: Clone + Send + Sync + 'static,
{
    /// Creates a new `Reader` instance.
    /// 
    /// # Parameters
    /// 
    /// * `f`: A function that takes a reference to the environment and returns a value.
    /// 
    /// # Type Parameters
    /// 
    /// * `A`: The return type of the function `f`.
    /// * `F`: The type of the function `f`.
    pub fn new<A, F>(f: F) -> Self 
    where
        A: Send + Sync + 'static,
        F: for<'a> Fn(&'a E) -> A + Send + Sync + 'static,
    {
        Reader {
            run: Arc::new(move |e| Arc::new(f(e)))
        }
    }

    /// Runs the Reader computation with the given environment.
    /// 
    /// # Parameters
    /// 
    /// * `e`: A reference to the environment.
    /// 
    /// # Returns
    /// 
    /// An `Arc<dyn Any + Send + Sync>` containing the result of the computation.
    pub fn run_reader(&self, e: &E) -> Arc<dyn Any + Send + Sync> {
        (self.run)(e)
    }

    /// Creates a Reader that returns the environment itself.
    /// 
    /// # Returns
    /// 
    /// A new `Reader<E>` that, when run, will return the environment.
    pub fn ask() -> Self {
        Reader::new(|e: &E| e.clone())
    }

    /// Creates a Reader that applies a function to the environment.
    /// 
    /// # Parameters
    /// 
    /// * `f`: A function that takes a reference to the environment and returns a value.
    /// 
    /// # Type Parameters
    /// 
    /// * `A`: The return type of the function `f`.
    /// * `F`: The type of the function `f`.
    /// 
    /// # Returns
    /// 
    /// A new `Reader<E>` that, when run, will apply `f` to the environment.
    pub fn asks<A, F>(f: F) -> Self
    where
        A: Send + Sync + 'static,
        F: for<'a> Fn(&'a E) -> A + Send + Sync + 'static,
    {
        Reader::new(f)
    }

    /// Modifies the environment before running a Reader.
    /// 
    /// # Parameters
    /// 
    /// * `f`: A function that takes a reference to the environment and returns a new environment.
    /// * `reader`: The Reader to run with the modified environment.
    /// 
    /// # Type Parameters
    /// 
    /// * `F`: The type of the function `f`.
    /// 
    /// # Returns
    /// 
    /// A new `Reader<E>` that, when run, will first apply `f` to the environment and then run `reader` with the result.
    pub fn local<F>(f: F, reader: Self) -> Self
    where
        F: for<'a> Fn(&'a E) -> E + Send + Sync + 'static,
    {
        Reader {
            run: Arc::new(move |e| {
                let new_env = f(e);
                reader.run_reader(&new_env)
            }),
        }
    }
}

impl<E: Clone + Send + Sync + 'static> TypeOps for Reader<E> {
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn equals(&self, _other: &AnyBox) -> bool {
        false
    }
}

impl<E: Clone + Send + Sync + 'static> HKT for Reader<E> {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Reader<E>>()
            .map(|x| Arc::new(x.clone()) as Arc<dyn Any + Send + Sync>)
    }
}

impl<E: Clone + Send + Sync + 'static> Functor for Reader<E> {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(Reader::new(move |e: &E| {
            let result = self_run(e);
            f(result)
        }))
    }
}

impl<E: Clone + Send + Sync + 'static> Pure for Reader<E> {
    fn pure(value: AnyBox) -> AnyBox {
        Arc::new(Reader::new(move |_: &E| value.clone()))
    }
}

impl<E: Clone + Send + Sync + 'static> Applicative for Reader<E> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let reader = self.clone();
        Arc::new(Reader::new(move |env| {
            let result = reader.run_reader(env);
            f(result)
        })) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(b_reader) = b.downcast_ref::<Reader<E>>() {
            let self_run = self.run.clone();
            let b_run = b_reader.run.clone();
            Arc::new(Reader::new(move |e: &E| {
                let a_result = self_run(e);
                let b_result = b_run(e);
                f(a_result, b_result)
            }))
        } else {
            Arc::new(self.clone())
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(b_reader), Some(c_reader)) = (b.downcast_ref::<Reader<E>>(), c.downcast_ref::<Reader<E>>()) {
            let self_run = self.run.clone();
            let b_run = b_reader.run.clone();
            let c_run = c_reader.run.clone();
            Arc::new(Reader::new(move |e: &E| {
                let a_result = self_run(e);
                let b_result = b_run(e);
                let c_result = c_run(e);
                f(a_result, b_result, c_result)
            }))
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<E: Clone + Send + Sync + 'static> Monad for Reader<E> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(Reader::new(move |e: &E| {
            let result = self_run(e);
            let next_reader = f(result.clone());
            if let Some(reader) = next_reader.downcast_ref::<Reader<E>>() {
                reader.run_reader(e)
            } else {
                result
            }
        }))
    }

    fn join(&self) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(Reader::new(move |e: &E| {
            let inner = self_run(e);
            if let Some(reader) = inner.downcast_ref::<Reader<E>>() {
                reader.run_reader(e)
            } else {
                inner
            }
        }))
    }
}

impl<E: Clone + Send + Sync + 'static> Identity for Reader<E> {
    fn identity() -> AnyBox {
        Arc::new(Reader::new(|e: &E| Arc::new(e.clone())))
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<E: Clone + Send + Sync + 'static> Category for Reader<E> {
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_reader) = other.downcast_ref::<Reader<E>>() {
            let self_run = self.run.clone();
            let other_run = other_reader.run.clone();
            Arc::new(Reader::new(move |e: &E| {
                let intermediate = other_run(e);
                if let Some(env) = intermediate.downcast_ref::<E>() {
                    self_run(&env.clone())
                } else {
                    intermediate
                }
            }))
        } else {
            Arc::new(self.clone())
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Reader::new(|e: &E| Arc::new(e.clone())))
    }
}
