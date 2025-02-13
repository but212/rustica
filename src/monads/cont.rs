use std::sync::Arc;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::identity::Identity;
use crate::category::composable::Composable;
use crate::fntype::{FnType, FnTrait};

/// The continuation monad.
///
/// # Type Parameters
/// * `R` - The return type of the continuation.
/// * `A` - The type to be computed asynchronously.
///
/// # Examples
/// ```rust
/// use rustica::monads::cont::Cont;
/// use rustica::fntype::{FnType, FnTrait};
/// 
/// fn main() {
///     let cont = Cont::new(FnType::new(|k: FnType<i32, i32>| k.call(1)));
///     let result = cont.run(FnType::new(|x: i32| x + 1));
///     assert_eq!(result, 2);
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The continuation function.
    ///
    /// This field holds the core logic of the continuation monad.
    /// It's a function that takes another function (the continuation)
    /// as an argument and returns a result of type `R`.
    pub run_cont: Arc<FnType<FnType<A, R>, R>>,
}

impl<R, A> Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new `Cont` instance.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation and returns a result.
    ///
    /// # Returns
    ///
    /// A new `Cont` instance.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function `f`.
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<FnType<A, R>, R>,
    {
        Cont {
            run_cont: Arc::new(FnType::new(move |k| f.call(k))),
        }
    }

    /// Executes the continuation with the given function.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a value of type `A` and returns a value of type `R`.
    ///
    /// # Returns
    ///
    /// The result of type `R` after applying the continuation.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function `f`.
    pub fn run<F>(self, f: F) -> R
    where
        F: FnTrait<A, R>,
    {
        self.run_cont.call(FnType::new(move |x| f.call(x)))
    }
}

impl<R, A> Pure<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<A, R>| k.call(value.clone()))),
        }
    }
}

impl<R, A> Functor<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B> + Clone,
    {
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<B, R>| {
                let f = f.clone();
                self.run_cont.call(FnType::new(move |x| k.call(f.call(x))))
            })),
        }
    }
}

impl<R, A> Applicative<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        let this = Arc::new(self);
        let mf = Arc::new(mf);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<B, R>| {
                let k = Arc::new(k);
                let this = Arc::clone(&this);
                mf.run_cont.call(FnType::new(move |f: F| {
                    let f = Arc::new(f);
                    let k = Arc::clone(&k);
                    let this = Arc::clone(&this);
                    this.run_cont.call(FnType::new(move |x| k.call(f.call(x))))
                }))
            })),
        }
    }

    fn lift2<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        let this = Arc::new(self);
        let b = Arc::new(b);
        let f = Arc::new(f);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<C, R>| {
                let k = Arc::new(k);
                let this = Arc::clone(&this);
                let b = Arc::clone(&b);
                let f = Arc::clone(&f);
                this.run_cont.call(FnType::new(move |a: A| {
                    let k = Arc::clone(&k);
                    let f = Arc::clone(&f);
                    let a = a.clone();
                    b.run_cont.call(FnType::new(move |b| {
                        k.call(f.call((a.clone(), b)))
                    }))
                }))
            })),
        }
    }

    fn lift3<B, C, D, F>(self, b: Self::Output<B>, c: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        let this = Arc::new(self);
        let b = Arc::new(b);
        let c = Arc::new(c);
        let f = Arc::new(f);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<D, R>| {
                let k = Arc::new(k);
                let this = Arc::clone(&this);
                let b = Arc::clone(&b);
                let c = Arc::clone(&c);
                let f = Arc::clone(&f);
                this.run_cont.call(FnType::new(move |a: A| {
                    let k = Arc::clone(&k);
                    let f = Arc::clone(&f);
                    let b = Arc::clone(&b);
                    let c = Arc::clone(&c);
                    let a = a.clone();
                    b.run_cont.call(FnType::new(move |b: B| {
                        let k = Arc::clone(&k);
                        let f = Arc::clone(&f);
                        let c = Arc::clone(&c);
                        let a = a.clone();
                        let b = b.clone();
                        c.run_cont.call(FnType::new(move |c: C| {
                            k.call(f.call((a.clone(), b.clone(), c.clone())))
                        }))
                    }))
                }))
            })),
        }
    }
}

impl<R, A> Monad<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<B, R>| {
                let k = Arc::new(k);
                let f = Arc::clone(&f);
                self.run_cont.call(FnType::new(move |a: A| {
                    let k = Arc::clone(&k);
                    f.call(a).run_cont.call((*k).clone())
                }))
            })),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(|x: A| x.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| g.call(x).bind(h.clone()))
    }
}

impl<R, A> HKT for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Cont<R, T> where T: ReturnTypeConstraints;
}

impl<R: ReturnTypeConstraints, A: ReturnTypeConstraints> Identity for Cont<R, A> {}

impl<R: ReturnTypeConstraints, A: ReturnTypeConstraints> Composable for Cont<R, A> {}

impl<R: ReturnTypeConstraints, A: ReturnTypeConstraints> Category for Cont<R, A> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;
}

impl<R: ReturnTypeConstraints, A: ReturnTypeConstraints> Arrow for Cont<R, A> {}