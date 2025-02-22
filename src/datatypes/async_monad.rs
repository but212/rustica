use crate::prelude::*;
use std::future::Future;
use std::fmt;
use std::sync::Arc;
use std::pin::Pin;
use crate::traits::hkt::AnyBox;

/// A monad for asynchronous computations
/// 
/// `AsyncM` represents a computation that will produce a value of type `A` asynchronously.
/// It encapsulates a `Future` that can be run to obtain the final value.
/// 
/// # Type Parameters
/// 
/// * `A`: The type of value that will be produced asynchronously
/// 
/// # Thread Safety
/// 
/// `AsyncM` is thread-safe and can be safely shared between threads:
/// - All internal state is immutable
/// - Future computations are wrapped in `Arc` for safe sharing
/// - All trait bounds ensure Send + Sync compliance
/// 
/// # Examples
/// 
/// ```
/// use rustica::datatypes::async_monad::AsyncM;
/// use rustica::prelude::*;
/// use std::time::Duration;
/// use tokio::time::sleep;
/// use std::sync::Arc;
/// 
/// # #[tokio::main]
/// # async fn main() {
/// let async_m = AsyncM::new(|| async {
///     sleep(Duration::from_secs(1)).await;
///     42
/// });
/// 
/// let result = AsyncM::new(|| async { 42 }).run().await;
/// assert_eq!(result, 42);
/// 
/// // Using implemented trait methods
/// let doubled = AsyncM::new(|| async { 42 }).fmap(Arc::new(|x: AnyBox| {
///     let value = x.downcast_ref::<i32>().unwrap();
///     Arc::new(*value * 2) as AnyBox
/// }));
/// let result = <AsyncM<i32> as Clone>::clone(&doubled.downcast_ref::<AsyncM<i32>>().unwrap()).run().await;
/// assert_eq!(result, 84);
/// 
/// let async_m2 = AsyncM::pure(&AsyncM::new(|| async { 0 }), Arc::new(10) as AnyBox);
/// let combined = AsyncM::lift3(
///     &AsyncM::new(|| async { 42 }),
///     async_m2,
///     AsyncM::pure(&AsyncM::new(|| async { 0 }), Arc::new(0) as AnyBox),
///     Arc::new(|x: AnyBox, y: AnyBox, _: AnyBox| {
///         let x_val = *x.downcast_ref::<i32>().unwrap();
///         let y_val = *y.downcast_ref::<i32>().unwrap();
///         Arc::new(x_val + y_val) as AnyBox
///     })
/// );
/// let result = <AsyncM<i32> as Clone>::clone(&combined.downcast_ref::<AsyncM<i32>>().unwrap()).run().await;
/// assert_eq!(result, 52);
/// # }
/// ```
#[derive(Clone)]
pub struct AsyncM<A: Send + Sync + Clone + 'static> {
    run: Arc<dyn Fn() -> Pin<Box<dyn Future<Output = A> + Send + Sync>> + Send + Sync>,
}

impl<A: Send + Sync + Clone + 'static> AsyncM<A> {
    /// Creates a new `AsyncM` from a function that produces a `Future`
    pub fn new<Fut, F>(f: F) -> Self
    where
        Fut: Future<Output = A> + Send + Sync + 'static,
        F: Fn() -> Fut + Clone + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        let run_fn = Arc::new(move || {
            let f = f.clone();
            Box::pin(async move { 
                let fut = f();
                fut.await 
            }) as Pin<Box<dyn Future<Output = A> + Send + Sync>>
        }) as Arc<dyn Fn() -> Pin<Box<dyn Future<Output = A> + Send + Sync>> + Send + Sync>;
        AsyncM { run: run_fn }
    }

    /// Runs the async computation and returns the result
    pub async fn run(self) -> A {
        (self.run)().await
    }
}

impl<A: Send + Sync + Clone + 'static> fmt::Debug for AsyncM<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AsyncM")
            .field("run", &"<future>")
            .finish()
    }
}

impl<A: Send + Sync + Clone + 'static> TypeOps for AsyncM<A> {
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn equals(&self, _other: &AnyBox) -> bool {
        false
    }
}

impl<A: Send + Sync + Clone + 'static> HKT for AsyncM<A> {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<AsyncM<A>>()
            .map(|x| Arc::new(x.clone()) as AnyBox)
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Identity for AsyncM<A> {
    fn identity() -> AnyBox {
        Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox)
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Functor for AsyncM<A> {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(AsyncM::new(move || {
            let f = f.clone();
            let self_run = self_run.clone();
            async move {
                let value = (self_run)().await;
                let boxed = Arc::new(value) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }
        })) as AnyBox
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Pure for AsyncM<A> {
    fn pure(value: AnyBox) -> AnyBox {
        if let Some(val) = value.downcast_ref::<A>() {
            let val = val.clone();
            Arc::new(AsyncM::new(move || {
                let val = val.clone();
                async move { val }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Applicative for AsyncM<A> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let fut = self.run.clone();
        let async_m = AsyncM::new(move || {
            let f = f.clone();
            let fut = fut.clone();
            async move {
                let x = (fut)().await;
                let x_box = Arc::new(x) as AnyBox;
                let result = f(x_box);
                result.downcast_ref::<A>().unwrap().clone()
            }
        });
        Arc::new(async_m) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(b_async) = b.downcast_ref::<AsyncM<A>>() {
            let self_run = self.run.clone();
            let b_run = b_async.run.clone();
            Arc::new(AsyncM::new(move || {
                let f = f.clone();
                let self_run = self_run.clone();
                let b_run = b_run.clone();
                async move {
                    let a_val = (self_run)().await;
                    let b_val = (b_run)().await;
                    let a_box = Arc::new(a_val) as AnyBox;
                    let b_box = Arc::new(b_val) as AnyBox;
                    if let Some(result) = f(a_box, b_box).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(b_async), Some(c_async)) = (b.downcast_ref::<AsyncM<A>>(), c.downcast_ref::<AsyncM<A>>()) {
            let self_run = self.run.clone();
            let b_run = b_async.run.clone();
            let c_run = c_async.run.clone();
            Arc::new(AsyncM::new(move || {
                let f = f.clone();
                let self_run = self_run.clone();
                let b_run = b_run.clone();
                let c_run = c_run.clone();
                async move {
                    let a_val = (self_run)().await;
                    let b_val = (b_run)().await;
                    let c_val = (c_run)().await;
                    let a_box = Arc::new(a_val) as AnyBox;
                    let b_box = Arc::new(b_val) as AnyBox;
                    let c_box = Arc::new(c_val) as AnyBox;
                    if let Some(result) = f(a_box, b_box, c_box).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Category for AsyncM<A> {
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_async) = other.downcast_ref::<AsyncM<A>>() {
            let self_run = self.run.clone();
            let other_run = other_async.run.clone();
            Arc::new(AsyncM::new(move || {
                let self_run = self_run.clone();
                let other_run = other_run.clone();
                async move {
                    let other_val = (other_run)().await;
                    let _ = (self_run)().await;
                    other_val
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Monad for AsyncM<A> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(AsyncM::new(move || {
            let f = f.clone();
            let self_run = self_run.clone();
            async move {
                let value = (self_run)().await;
                let boxed = Arc::new(value) as AnyBox;
                if let Some(next_async) = f(boxed).downcast_ref::<AsyncM<A>>() {
                    let next_run = next_async.run.clone();
                    (next_run)().await
                } else {
                    A::default()
                }
            }
        })) as AnyBox
    }

    fn join(&self) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(AsyncM::new(move || {
            let self_run = self_run.clone();
            async move {
                let inner = (self_run)().await;
                if let Some(inner_async) = (Arc::new(inner) as AnyBox).downcast_ref::<AsyncM<A>>() {
                    let inner_run = inner_async.run.clone();
                    (inner_run)().await
                } else {
                    A::default()
                }
            }
        })) as AnyBox
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Arrow for AsyncM<A> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = func.clone();
            Arc::new(AsyncM::new(move || {
                let func = func.clone();
                async move {
                    if let Some(result) = func(Arc::new(A::default()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = func.clone();
            Arc::new(AsyncM::new(move || {
                let func = func.clone();
                async move {
                    if let Some(result) = func(Arc::new(A::default()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = func.clone();
            Arc::new(AsyncM::new(move || {
                let func = func.clone();
                async move {
                    if let Some(result) = func(Arc::new(A::default()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        if let (Some(f_func), Some(_g_func)) = (
            f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
            g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
        ) {
            let f_func = f_func.clone();
            Arc::new(AsyncM::new(move || {
                let f_func = f_func.clone();
                async move {
                    let f_result = f_func(Arc::new(A::default()) as AnyBox);
                    if let Some(f_val) = f_result.downcast_ref::<A>() {
                        f_val.clone()
                    } else {
                        A::default()
                    }
                }
            })) as AnyBox
        } else {
            Arc::new(AsyncM::new(|| async { A::default() })) as AnyBox
        }
    }
}

impl<A: Send + Sync + Clone + Default + 'static> Composable for AsyncM<A> {
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = self.run.clone();
        Arc::new(AsyncM::new(move || {
            let f = f.clone();
            let self_run = self_run.clone();
            async move {
                let value = (self_run)().await;
                let boxed = Arc::new(value) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            }
        })) as AnyBox
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        let f = f.clone();
        let g = g.clone();
        Arc::new(move |x| g(f(x.clone())))
    }
}