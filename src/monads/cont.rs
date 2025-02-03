use std::fmt::{self, Debug};
use std::sync::Arc;

use crate::category::{Applicative, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, MonadFn};

/// The continuation monad.
#[derive(Clone)]
pub struct Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The continuation function
    pub run_cont: SendSyncFn<SendSyncFn<A, R>, R>,
}

impl<R, A> PartialEq for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let k = SendSyncFn::new(move |_x: A| R::default());
        let r1 = self.run_cont.call(k.clone());
        let r2 = other.run_cont.call(k);
        r1 == r2
    }
}

impl<R, A> Debug for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cont")
            .field("run_cont", &"<function>")
            .finish()
    }
}

impl<R, A> Default for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        Cont {
            run_cont: SendSyncFn::default(),
        }
    }
}

impl<R, A> Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new continuation.
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<SendSyncFn<A, R>, R>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: SendSyncFn::new(move |k| f.call(k)),
        }
    }

    /// Runs the continuation with the given continuation function.
    pub fn run<F>(self, f: F) -> R
    where
        F: SendSyncFnTrait<A, R>,
    {
        let f = Arc::new(f);
        self.run_cont.call(SendSyncFn::new(move |x| f.call(x)))
    }
}

impl<R, A> Pure<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A>
    {
        let value = Arc::new(value);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<A, R>| k.call((*value).clone())),
        }
    }
}

impl<R, A> Functor<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<B, R>| {
                let f = Arc::clone(&f);
                self.run_cont.call(SendSyncFn::new(move |x| k.call(f.call(x))))
            }),
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
        F: SendSyncFnTrait<A, B> + Default,
    {
        let this = Arc::new(self);
        let mf = Arc::new(mf);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<B, R>| {
                let k = Arc::new(k);
                let this = Arc::clone(&this);
                mf.run_cont.call(SendSyncFn::new(move |f: F| {
                    let f = Arc::new(f);
                    let k = Arc::clone(&k);
                    let this = Arc::clone(&this);
                    this.run_cont.call(SendSyncFn::new(move |x| k.call(f.call(x))))
                }))
            }),
        }
    }

    fn lift2<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, SendSyncFn<B, C>>,
    {
        let this = Arc::new(self);
        let f = Arc::new(f);
        let b = Arc::new(b);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<C, R>| {
                let k = Arc::new(k);
                let f = Arc::clone(&f);
                let b = Arc::clone(&b);
                let this = Arc::clone(&this);
                this.run_cont.call(SendSyncFn::new(move |x: A| {
                    let f = Arc::clone(&f);
                    let b = Arc::clone(&b);
                    let k = Arc::clone(&k);
                    let fx = f.call(x);
                    b.run_cont.call(SendSyncFn::new(move |y: B| k.call(fx.call(y))))
                }))
            }),
        }
    }

    fn lift3<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        let this = Arc::new(self);
        let f = Arc::new(f);
        let b = Arc::new(b);
        let c = Arc::new(c);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<D, R>| {
                let k = Arc::new(k);
                let f = Arc::clone(&f);
                let b = Arc::clone(&b);
                let c = Arc::clone(&c);
                let this = Arc::clone(&this);
                this.run_cont.call(SendSyncFn::new(move |x: A| {
                    let f = Arc::clone(&f);
                    let b = Arc::clone(&b);
                    let c = Arc::clone(&c);
                    let k = Arc::clone(&k);
                    let fx = f.call(x);
                    b.run_cont.call(SendSyncFn::new(move |y: B| {
                        let c = Arc::clone(&c);
                        let k = Arc::clone(&k);
                        let fx = fx.clone();
                        let fxy = fx.call(y);
                        c.run_cont.call(SendSyncFn::new(move |z: C| k.call(fxy.call(z))))
                    }))
                }))
            }),
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
        F: MonadFn<A, B, Cont<R, B>>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: SendSyncFn::new(move |k: SendSyncFn<B, R>| {
                let k = Arc::new(k);
                let f = Arc::clone(&f);
                self.run_cont.call(SendSyncFn::new(move |a: A| {
                    let k = Arc::clone(&k);
                    f.call(a).run_cont.call((*k).clone())
                }))
            }),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        let f = SendSyncFn::new(|x: A| x.into());
        self.bind(f)
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Cont<R, B>>,
        H: MonadFn<B, C, Cont<R, C>>,
    {
        SendSyncFn::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<R, A> HKT for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Cont<R, T> where T: ReturnTypeConstraints;
}
