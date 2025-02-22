use std::sync::Arc;
use std::any::Any;

use crate::traits::{
    hkt::{HKT, AnyBox},
    applicative::Applicative,
    monad::Monad,
    identity::Identity,
    pure::Pure,
    functor::Functor,
    arrow::Arrow,
    composable::Composable,
    category::Category,
    bifunctor::Bifunctor,
    comonad::Comonad,
    foldable::Foldable,
    traversable::Traversable,
    semigroup::Semigroup,
    monoid::Monoid,
};

/// Represents a stateful computation.
///
/// `State<S>` encapsulates a function that takes a state of type `S` and returns
/// a new state along with a result value.
#[derive(Clone)]
pub struct State<S> {
    /// The internal function that performs the stateful computation.
    run: Arc<dyn Fn(S) -> (S, Arc<dyn Any + Send + Sync>) + Send + Sync>,
}

impl<S> State<S>
where
    S: 'static + Clone + Send + Sync,
{
    /// Creates a new `State` instance.
    ///
    /// # Arguments
    ///
    /// * `run` - A function that takes a state and returns a tuple of the new state and a result.
    ///
    /// # Returns
    ///
    /// A new `State` instance.
    pub fn new<A>(run: impl Fn(S) -> (S, A) + Send + Sync + 'static) -> Self
    where
        A: 'static + Send + Sync,
    {
        State {
            run: Arc::new(move |s| {
                let (s2, a) = run(s);
                (s2, Arc::new(a) as Arc<dyn Any + Send + Sync>)
            }),
        }
    }

    /// Runs the stateful computation.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state.
    ///
    /// # Returns
    ///
    /// A tuple containing the new state and the result value.
    pub fn run(&self, s: S) -> (S, Arc<dyn Any + Send + Sync>) {
        (self.run)(s)
    }

    /// Maps the result of the stateful computation.
    ///
    /// # Arguments
    ///
    /// * `f` - A function to apply to the result value.
    ///
    /// # Returns
    ///
    /// A new `State` instance with the mapped result.
    pub fn map<B>(&self, f: impl Fn(Arc<dyn Any + Send + Sync>) -> B + Send + Sync + 'static) -> State<S>
    where
        B: 'static + Send + Sync,
    {
        let run_clone = self.run.clone();
        State::new(move |s| {
            let (s2, a) = run_clone(s);
            (s2, f(a))
        })
    }

    /// Chains two stateful computations.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes the result of this computation and returns a new `State`.
    ///
    /// # Returns
    ///
    /// A new `State` instance representing the chained computation.
    pub fn flat_map<B>(&self, f: impl Fn(Arc<dyn Any + Send + Sync>) -> State<S> + Send + Sync + 'static) -> State<S>
    where
        B: 'static + Send + Sync,
    {
        let run_clone = self.run.clone();
        State::new(move |s| {
            let (s2, a) = run_clone(s);
            f(a).run(s2)
        })
    }
}

impl<S> HKT for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<State<S>>().map(|s| Arc::new(s.clone()) as AnyBox)
    }
}

impl<S> Pure for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn pure(a: Arc<dyn Any + Send + Sync>) -> AnyBox {
        Arc::new(State::new(move |s: S| (s, a.clone()))) as AnyBox
    }
}

impl<S> Identity for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn identity() -> AnyBox {
        Arc::new(State::new(|s: S| (s, Arc::new(()) as Arc<dyn Any + Send + Sync>))) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<S> Functor for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn fmap(&self, f: Arc<dyn Fn(Arc<dyn Any + Send + Sync>) -> Arc<dyn Any + Send + Sync> + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (s2, f(a))
        })) as AnyBox
    }
}

impl<S> Applicative for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let state = self.clone();
        Arc::new(State::new(move |s| {
            let (s1, a) = state.run(s);
            let result = f(a);
            (s1, result)
        })) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        let b = b.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s.clone());
            if let Some(state_b) = b.downcast_ref::<State<S>>() {
                let (s3, b) = state_b.run(s2);
                (s3, f(Arc::new(a) as AnyBox, Arc::new(b) as AnyBox))
            } else {
                (s2, Arc::new(a) as AnyBox)
            }
        })) as AnyBox
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        let b = b.clone();
        let c = c.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s.clone());
            if let (Some(state_b), Some(state_c)) = (b.downcast_ref::<State<S>>(), c.downcast_ref::<State<S>>()) {
                let (s3, b) = state_b.run(s2);
                let (s4, c) = state_c.run(s3);
                (s4, f(Arc::new(a) as AnyBox, Arc::new(b) as AnyBox, Arc::new(c) as AnyBox))
            } else {
                (s2, Arc::new(a) as AnyBox)
            }
        })) as AnyBox
    }
}

impl<S> Monad for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            if let Some(state) = f(Arc::new(a) as AnyBox).downcast_ref::<State<S>>() {
                state.run(s2)
            } else {
                (s2, Arc::new(()) as Arc<dyn Any + Send + Sync>)
            }
        })) as AnyBox
    }

    fn join(&self) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            if let Some(state) = a.downcast_ref::<State<S>>() {
                state.run(s2)
            } else {
                (s2, Arc::new(()) as Arc<dyn Any + Send + Sync>)
            }
        })) as AnyBox
    }
}

impl<S> Arrow for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn arrow(&self, f: AnyBox) -> AnyBox {
        let run_clone = self.run.clone();
        let f = f.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                (s2, func(Arc::new(a) as AnyBox))
            } else {
                (s2, Arc::new(a) as AnyBox)
            }
        })) as AnyBox
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        let run_clone = self.run.clone();
        let f = f.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                (s2, func(Arc::new(a) as AnyBox))
            } else {
                (s2, Arc::new(a) as AnyBox)
            }
        })) as AnyBox
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        let run_clone = self.run.clone();
        let f = f.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                (s2, func(Arc::new(a) as AnyBox))
            } else {
                (s2, Arc::new(a) as AnyBox)
            }
        })) as AnyBox
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        let run_clone = self.run.clone();
        let f = f.clone();
        let g = g.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            let f_result = if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                func(Arc::new(a.clone()) as AnyBox)
            } else {
                Arc::new(a.clone()) as AnyBox
            };
            let g_result = if let Some(func) = g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                func(Arc::new(a) as AnyBox)
            } else {
                Arc::new(a) as AnyBox
            };
            (s2, Arc::new((f_result, g_result)) as Arc<dyn Any + Send + Sync>)
        })) as AnyBox
    }
}

impl<S> Composable for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        let f = f.clone();
        let g = g.clone();
        Arc::new(move |x| g(f(x)))
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            let result = f(Arc::new(a) as AnyBox);
            (s2, result)
        })) as AnyBox
    }
}

impl<S> Category for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_state) = other.downcast_ref::<State<S>>() {
            let self_run = self.run.clone();
            let other_run = other_state.run.clone();
            Arc::new(State::new(move |s: S| {
                let (s2, _) = other_run(s);
                self_run(s2)
            }))
        } else {
            Arc::new(self.clone())
        }
    }

    fn identity_morphism() -> AnyBox {
        let state = S::default();
        Arc::new(State::new(move |s: S| (s, Arc::new(state.clone()))))
    }
}

impl<S> Bifunctor for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (f(Arc::new(s2)).downcast_ref::<S>().unwrap().clone(), g(a))
        }))
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (f(Arc::new(s2)).downcast_ref::<S>().unwrap().clone(), a)
        }))
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (s2, f(a))
        }))
    }
}

impl<S> Comonad for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn extract(&self) -> AnyBox {
        let (_, a) = self.run(S::default());
        a
    }

    fn duplicate(&self) -> AnyBox {
        let self_clone = self.clone();
        Arc::new(State::new(move |s: S| {
            (s.clone(), Arc::new(self_clone.clone()))
        }))
    }

    fn extend(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let self_clone = self.clone();
        Arc::new(State::new(move |s: S| {
            (s.clone(), f(Arc::new(self_clone.clone())))
        }))
    }
}

impl<S> Foldable for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let (_, a) = self.run(S::default());
        f(init, a)
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let (_, a) = self.run(S::default());
        f(a, init)
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let (_, a) = self.run(S::default());
        f(a)
    }
}

impl<S> Traversable for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static,
    {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (s2, f(a))
        }))
    }

    fn distribute(&self) -> AnyBox {
        let run_clone = self.run.clone();
        Arc::new(State::new(move |s: S| {
            let (s2, a) = run_clone(s);
            (s2, a)
        }))
    }
}

impl<S> Semigroup for State<S>
where
    S: 'static + Clone + Send + Sync,
{
    fn combine(&self, other: AnyBox) -> AnyBox {
        if let Some(other_state) = other.downcast_ref::<State<S>>() {
            let self_run = self.run.clone();
            let other_run = other_state.run.clone();
            Arc::new(State::new(move |s: S| {
                let (s2, a1) = self_run(s);
                let (s3, a2) = other_run(s2);
                (s3, Arc::new((a1, a2)))
            }))
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<S> Monoid for State<S>
where
    S: 'static + Clone + Send + Sync + Default,
{
    fn empty(&self) -> AnyBox {
        Arc::new(State::new(|s: S| (s, Arc::new(()))))
    }
}
