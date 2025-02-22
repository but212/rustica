use std::sync::Arc;
use crate::traits::hkt::{TypeOps, AnyBox, HKT};
use crate::traits::pure::Pure;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::monad::Monad;
use crate::traits::contravariant_functor::ContravariantFunctor;
use crate::traits::natural::NaturalTransformation;
use crate::traits::evaluate::Evaluate;
use crate::traits::identity::Identity;
use crate::prelude::*;

/// Continuation monad implementation
/// 
/// Represents computations that can be composed with continuations.
/// This structure encapsulates a function that takes a continuation
/// and returns a result, allowing for powerful control flow manipulations.
/// 
/// Type Parameters:
/// - `R`: The return type of the continuation
/// - `A`: The value type being continued
/// 
/// # Examples
/// 
/// ```
/// use rustica::datatypes::cont::Cont;
/// use std::sync::Arc;
/// 
/// let cont: Cont<i32, i32> = Cont::new(|k| {
///     Cont::new(|k2| {
///         Cont::callcc(
///             &Cont::new(|_| 0),
///             |exit: Arc<dyn Fn(i32) -> i32 + Send + Sync>| {
///                 let some_condition = true; // Example condition
///                 if some_condition {
///                     exit(42) // Early exit
///                 } else {
///                     10 // Normal continuation
///                 }
///             }
///         ).run(k2)
///     }).run(k)
/// });
/// 
/// let result = cont.run(Arc::new(|x| x * 2));
/// assert_eq!(result, 84);
/// ```
#[derive(Clone)]
pub struct Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    /// The continuation function
    run: Arc<dyn Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync>,
}

impl<R, A> Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    /// Creates a new continuation
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes a continuation and returns a result
    /// 
    /// # Returns
    /// 
    /// A new `Cont` instance
    pub fn new<F>(f: F) -> Self 
    where
        F: Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static,
    {
        Self {
            run: Arc::new(f)
        }
    }

    /// Runs the continuation with a given continuation function
    /// 
    /// # Arguments
    /// 
    /// * `k` - The continuation function to run
    /// 
    /// # Returns
    /// 
    /// The result of running the continuation
    pub fn run(&self, k: Arc<dyn Fn(A) -> R + Send + Sync>) -> R {
        (self.run)(k)
    }

    /// Call-with-current-continuation (callcc)
    /// 
    /// Captures the current continuation and passes it to the given function.
    /// This allows for powerful control flow operations like early return or backtracking.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes the current continuation and returns a result
    /// 
    /// # Returns
    /// 
    /// A new `Cont` instance
    /// 
    /// # Example
    /// 
    /// ```
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    /// 
    /// let cont: Cont<i32, i32> = Cont::new(|k| {
    ///     Cont::new(|k2| {
    ///         Cont::callcc(&Cont::new(|_| 0), |exit: Arc<dyn Fn(i32) -> i32 + Send + Sync>| {
    ///             let some_condition = true; // Example condition
    ///             if some_condition {
    ///                 exit(42) // Early exit
    ///             } else {
    ///                 10 // Normal continuation
    ///             }
    ///         }).run(k2)
    ///     }).run(k)
    /// });
    /// 
    /// let result = cont.run(Arc::new(|x| x * 2));
    /// assert_eq!(result, 84);
    /// ```
    pub fn callcc<F>(&self, f: F) -> Self 
    where
        F: Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static,
    {
        Self::new(move |k| {
            f(k)
        })
    }

    /// Helper to chain continuations
    /// 
    /// This function allows composing two continuations sequentially,
    /// where the result of the first continuation is passed to the second.
    /// It is similar to bind but with better type inference in some cases.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes the result of this continuation and returns a new continuation
    /// 
    /// # Returns
    /// 
    /// A new `AnyBox` containing the chained continuation
    /// 
    /// # Example
    /// 
    /// ```
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::traits::hkt::AnyBox;
    /// use std::sync::Arc;
    /// 
    /// let cont1: Cont<i32, i32> = Cont::new(|k| k(5));
    /// let cont2 = cont1.chain(Arc::new(|x| {
    ///     Arc::new(Cont::new(move |k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| k(x.downcast_ref::<i32>().unwrap() * 2))) as AnyBox
    /// }));
    /// ```
    pub fn chain(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = Arc::clone(&self.run);
        Arc::new(Self::new(move |k| {
            let f = Arc::clone(&f);
            let k = Arc::clone(&k);
            self_run(Arc::new(move |a| {
                let k = Arc::clone(&k);
                let a = Arc::new(a.clone()) as AnyBox;
                if let Some(cont) = f(a).downcast_ref::<Self>() {
                    let cont_run = Arc::clone(&cont.run);
                    cont_run(k)
                } else {
                    k(A::default())
                }
            }))
        })) as AnyBox
    }
}

impl<R, A> Default for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn default() -> Self {
        Self::new(|_| R::default())
    }
}

impl<R, A> TypeOps for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn clone_box(&self) -> AnyBox {
        Arc::new((*self).clone()) as AnyBox
    }

    fn equals(&self, other: &AnyBox) -> bool {
        other.downcast_ref::<Self>()
            .map_or(false, |other| Arc::ptr_eq(&self.run, &other.run))
    }
}

impl<R, A> HKT for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn apply_type(&self) -> AnyBox {
        self.clone_box()
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Self>().map(|x| x.clone_box())
    }
}

impl<R, A> Pure for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn pure(a: AnyBox) -> AnyBox {
        if let Some(val) = a.downcast_ref::<A>() {
            let val = val.clone();
            Arc::new(Self::new(move |k| {
                let k = Arc::clone(&k);
                k(val.clone())
            })) as AnyBox
        } else {
            Arc::new(Self::new(move |k| {
                let k = Arc::clone(&k);
                k(A::default())
            })) as AnyBox
        }
    }
}

impl<R, A> Functor for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = Arc::clone(&self.run);
        Arc::new(Self::new(move |k| {
            let f2 = Arc::clone(&f);
            let k2 = Arc::clone(&k);
            self_run(Arc::new(move |a| {
                let boxed = Arc::new(a.clone()) as AnyBox;
                if let Some(result) = f2(boxed).downcast_ref::<A>() {
                    k2(result.clone())
                } else {
                    k2(A::default())
                }
            }))
        })) as AnyBox
    }
}

impl<R, A> Applicative for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let cont = self.clone();
        let new_cont = Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            let f = f.clone();
            let k2 = Arc::new(move |x: A| {
                let x_box = Arc::new(x) as AnyBox;
                let result = f(x_box);
                if let Some(a) = result.downcast_ref::<A>() {
                    k(a.clone())
                } else {
                    R::default()
                }
            });
            (cont.run)(k2)
        });
        Arc::new(new_cont) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(other) = b.downcast_ref::<Self>() {
            let self_run = Arc::clone(&self.run);
            let other_run = Arc::clone(&other.run);
            let f = Arc::clone(&f);
            Arc::new(Self::new(move |k| {
                let k2 = Arc::clone(&k);
                let f2 = Arc::clone(&f);
                let other_run2 = Arc::clone(&other_run);
                self_run(Arc::new(move |a| {
                    let k3 = Arc::clone(&k2);
                    let f3 = Arc::clone(&f2);
                    let other_run3 = Arc::clone(&other_run2);
                    let a = a.clone();
                    other_run3(Arc::new(move |b| {
                        let a_boxed = Arc::new(a.clone()) as AnyBox;
                        let b_boxed = Arc::new(b.clone()) as AnyBox;
                        if let Some(result) = f3(a_boxed, b_boxed).downcast_ref::<A>() {
                            k3(result.clone())
                        } else {
                            k3(A::default())
                        }
                    }))
                }))
            })) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(other1), Some(other2)) = (b.downcast_ref::<Self>(), c.downcast_ref::<Self>()) {
            let self_run = Arc::clone(&self.run);
            let other1_run = Arc::clone(&other1.run);
            let other2_run = Arc::clone(&other2.run);
            let f = Arc::clone(&f);
            Arc::new(Self::new(move |k| {
                let k2 = Arc::clone(&k);
                let f2 = Arc::clone(&f);
                let other1_run2 = Arc::clone(&other1_run);
                let other2_run2 = Arc::clone(&other2_run);
                self_run(Arc::new(move |a| {
                    let k3 = Arc::clone(&k2);
                    let f3 = Arc::clone(&f2);
                    let other1_run3 = Arc::clone(&other1_run2);
                    let other2_run3 = Arc::clone(&other2_run2);
                    let a = a.clone();
                    other1_run3(Arc::new(move |b| {
                        let k4 = Arc::clone(&k3);
                        let f4 = Arc::clone(&f3);
                        let other2_run4 = Arc::clone(&other2_run3);
                        let a = a.clone();
                        let b = b.clone();
                        other2_run4(Arc::new(move |c| {
                            let a_boxed = Arc::new(a.clone()) as AnyBox;
                            let b_boxed = Arc::new(b.clone()) as AnyBox;
                            let c_boxed = Arc::new(c.clone()) as AnyBox;
                            if let Some(result) = f4(a_boxed, b_boxed, c_boxed).downcast_ref::<A>() {
                                k4(result.clone())
                            } else {
                                k4(A::default())
                            }
                        }))
                    }))
                }))
            })) as AnyBox
        } else {
            self.clone_box()
        }
    }
}

impl<R, A> Category for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other) = other.downcast_ref::<Self>() {
            let self_run = Arc::clone(&self.run);
            let other_run = Arc::clone(&other.run);
            Arc::new(Self::new(move |k| {
                let k2 = Arc::clone(&k);
                let other_run2 = Arc::clone(&other_run);
                self_run(Arc::new(move |_a| {
                    let k3 = Arc::clone(&k2);
                    other_run2(Arc::new(move |b| k3(b)))
                }))
            })) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Self::new(|k| k(A::default()))) as AnyBox
    }
}

impl<R, A> Composable for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.chain(f)
    }
}

impl<R, A> Arrow for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    /// Implementation of Arrow for Cont
    /// 
    /// This implements the Arrow type class for continuations.
    /// Arrows generalize functions to include effects and composition.
    /// The arrow operation lifts a pure function into the continuation context,
    /// while first, second, and split handle parallel composition.
    fn arrow(&self, f: AnyBox) -> AnyBox {
        Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            if let Some(f_fn) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                let input = Arc::new(A::default()) as AnyBox;
                if let Some(result) = f_fn(input).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    R::default()
                }
            } else {
                R::default()
            }
        })) as AnyBox
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = Arc::clone(func);
            Arc::new(Self::new(move |k| {
                let k = Arc::clone(&k);
                let func = Arc::clone(&func);
                let input = Arc::new(A::default()) as AnyBox;
                if let Some(result) = func(input).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    k(A::default())
                }
            })) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = Arc::clone(func);
            Arc::new(Self::new(move |k| {
                let k = Arc::clone(&k);
                let func = Arc::clone(&func);
                let input = Arc::new(A::default()) as AnyBox;
                if let Some(result) = func(input).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    k(A::default())
                }
            })) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        let first = self.first(f);
        if let Some(cont1) = first.downcast_ref::<Self>() {
            let second = self.second(g);
            if let Some(cont2) = second.downcast_ref::<Self>() {
                let cont1_run = Arc::clone(&cont1.run);
                let cont2_run = Arc::clone(&cont2.run);
                Arc::new(Self::new(move |k| {
                    let k = Arc::clone(&k);
                    let cont2_run = Arc::clone(&cont2_run);
                    cont1_run(Arc::new(move |a| {
                        let k = Arc::clone(&k);
                        let _a = a.clone();
                        cont2_run(Arc::new(move |b| {
                            let k = Arc::clone(&k);
                            k(b)
                        }))
                    }))
                })) as AnyBox
            } else {
                self.clone_box()
            }
        } else {
            self.clone_box()
        }
    }
}

impl<R, A> Identity for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    /// Implementation of Identity for Cont
    /// 
    /// Provides identity operations for continuations.
    /// The identity operation returns the continuation unchanged,
    /// while map_identity applies a function to the continuation.
    fn identity() -> AnyBox {
        Arc::new(Cont::new(|k: Arc<dyn Fn(A) -> R + Send + Sync>| k(A::default()))) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(Cont::new(|k: Arc<dyn Fn(A) -> R + Send + Sync>| k(A::default()))) as AnyBox)
    }
}

impl<R, A> Monad for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    /// Implementation of Monad for Cont
    /// 
    /// This implements the Monad type class for continuations.
    /// The bind operation sequences computations by passing the result of one
    /// continuation to another, while join flattens nested continuations.
    /// 
    /// The bind operation is particularly important as it allows composing
    /// continuations in a way that maintains their sequential nature while
    /// properly handling the continuation passing style.
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_run = Arc::clone(&self.run);
        Arc::new(Self::new(move |k| {
            let f = Arc::clone(&f);
            let k = Arc::clone(&k);
            self_run(Arc::new(move |a: A| {
                let a_clone = a.clone();
                let boxed = Arc::new(a_clone) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<Self>() {
                    let result_run = Arc::clone(&result.run);
                    result_run(Arc::clone(&k))
                } else {
                    k(a)
                }
            }))
        })) as AnyBox
    }

    fn join(&self) -> AnyBox {
        let cont = self.clone();
        Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            (cont.run)(Arc::new(move |inner: A| {
                let boxed = Arc::new(inner) as AnyBox;
                if let Some(inner_cont) = boxed.downcast_ref::<Cont<R, A>>() {
                    (inner_cont.run)(k.clone())
                } else {
                    R::default()
                }
            }))
        })) as AnyBox
    }
}

/// Implementation of ContravariantFunctor for Cont
/// 
/// This allows mapping over the input type of the continuation in a contravariant way.
/// The contramap operation takes a function `f: B -> A` and a continuation `Cont<R, A>`
/// and produces a continuation `Cont<R, B>`.
impl<R, A> ContravariantFunctor for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn contramap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let cont = self.clone();
        Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            let f = f.clone();
            (cont.run)(Arc::new(move |x: A| {
                let boxed = Arc::new(x) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    R::default()
                }
            }))
        })) as AnyBox
    }
}

/// Implementation of NaturalTransformation for Cont
/// 
/// This provides natural transformations between continuation types.
/// A natural transformation η: F ~> G between functors F and G must satisfy
/// the naturality condition: η ∘ fmap(f) = fmap(f) ∘ η for all morphisms f.
impl<R, A> NaturalTransformation for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn transform(&self, other: AnyBox) -> AnyBox {
        let cont = self.clone();
        if let Some(_other_cont) = other.downcast_ref::<Cont<R, A>>() {
            Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
                (cont.run)(k)
            })) as AnyBox
        } else {
            Arc::new(cont) as AnyBox
        }
    }
}

/// Implementation of Evaluate for Cont
/// 
/// This provides methods to evaluate continuations with different strategies.
/// The evaluate method runs the continuation with a default continuation,
/// while evaluate_with allows specifying a custom environment.
impl<R, A> Evaluate for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static,
{
    fn evaluate(&self) -> AnyBox {
        let cont = self.clone();
        let result = (cont.run)(Arc::new(|x: A| {
            let boxed = Arc::new(x) as AnyBox;
            if let Some(result) = boxed.downcast_ref::<R>() {
                result.clone()
            } else {
                R::default()
            }
        }));
        Arc::new(result) as AnyBox
    }
}

impl<R, A> Bifunctor for Cont<R, A>
where
    R: TypeOps + Default + Clone + 'static,
    A: TypeOps + Default + Clone + 'static
{
    fn bimap(
            &self,
            f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
            g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
        ) -> AnyBox {
        let cont = self.clone();
        Arc::new(Cont::new(move |_k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            let f = f.clone();
            let g = g.clone();
            (cont.run)(Arc::new(move |x: A| {
                let boxed = Arc::new(x) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    if let Some(final_result) = g(Arc::new(result.clone()) as AnyBox).downcast_ref::<R>() {
                        final_result.clone()
                    } else {
                        R::default()
                    }
                } else {
                    R::default()
                }
            }))
        })) as AnyBox
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let cont = self.clone();
        Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            let f = f.clone();
            (cont.run)(Arc::new(move |x: A| {
                let boxed = Arc::new(x) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    R::default()
                }
            }))
        })) as AnyBox
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let cont = self.clone();
        Arc::new(Cont::new(move |k: Arc<dyn Fn(A) -> R + Send + Sync>| {
            let f = f.clone();
            (cont.run)(Arc::new(move |x: A| {
                let boxed = Arc::new(x) as AnyBox;
                if let Some(result) = f(boxed).downcast_ref::<A>() {
                    k(result.clone())
                } else {
                    R::default()
                }
            }))
        })) as AnyBox
    }
}