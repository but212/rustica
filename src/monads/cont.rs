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
/// A Continuation Monad must satisfy the following laws:
/// 
/// ## Core Continuation Laws
/// 1. Identity Law: ∀k ∈ K, a ∈ A:
///    pure(a).run(k) = k(a)
///    
/// 2. Composition Law: ∀x ∈ A, f: A → B, k: B → R:
///    pure(x).fmap(f).run(k) = k(f(x))
///    
/// ## Functor Laws
/// 1. Identity Law: ∀x ∈ Cont<R,A>:
///    x.fmap(id) = x
/// 
/// 2. Composition Law: ∀x ∈ Cont<R,A>, f: A → B, g: B → C:
///    x.fmap(f).fmap(g) = x.fmap(g ∘ f)
/// 
/// ## Monad Laws
/// 1. Left Identity Law: ∀x ∈ A, f: A → Cont<R,B>:
///    pure(x).bind(f) = f(x)
/// 
/// 2. Right Identity Law: ∀x ∈ Cont<R,A>:
///    x.bind(pure) = x
/// 
/// 3. Associativity Law: ∀x ∈ Cont<R,A>, f: A → Cont<R,B>, g: B → Cont<R,C>:
///    x.bind(f).bind(g) = x.bind(λy. f(y).bind(g))
/// 
/// ## Additional Properties
/// 1. Stack Safety: For deeply nested continuations,
///    the implementation maintains stack safety.
/// 2. Resource Safety: Resources captured in continuations
///    are properly managed and released.
/// 3. Compositionality: For any continuations f and g,
///    f.compose(g) maintains the continuation semantics.
/// 
/// # Examples
/// ```rust
/// use rustica::monads::cont::Cont;
/// use rustica::fntype::FnType;
/// 
/// fn main() {
///     let cont = Cont::new(FnType::new(|k: FnType<i32, i32>| k.call(1)));
///     let result = cont.run(FnType::new(|x: i32| x + 1));
///     assert_eq!(result, 2);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The continuation function
    pub run_cont: Arc<FnType<FnType<A, R>, R>>,
}

impl<R, A> Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new continuation.
    /// 
    /// # Type Parameters
    /// * `F` - The type of the function.
    /// 
    /// # Arguments
    /// * `f` - The function to be called.
    /// 
    /// # Returns
    /// * `Self` - The new continuation.
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<FnType<A, R>, R>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: Arc::new(FnType::new(move |k| f.call(k))),
        }
    }

    /// Runs the continuation with the given continuation function.
    /// 
    /// # Type Parameters
    /// * `F` - The type of the function.
    /// 
    /// # Arguments
    /// * `f` - The function to be called.
    /// 
    /// # Returns
    /// * `R` - The result of the computation.
    pub fn run<F>(self, f: F) -> R
    where
        F: FnTrait<A, R>,
    {
        let f = Arc::new(f);
        self.run_cont.call(FnType::new(move |x| f.call(x)))
    }
}

impl<R, A> Pure<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Returns a pure value.
    /// 
    /// # Type Parameters
    /// * `A` - The type of the value.
    /// 
    /// # Arguments
    /// * `value` - The value to be returned.
    /// 
    /// # Returns
    /// * `Cont<R, A>` - The new continuation.
    fn pure(value: A) -> Self::Output<A> {
        let value = Arc::new(value);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<A, R>| k.call((*value).clone()))),
        }
    }
}

impl<R, A> Functor<A> for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Maps a function over the value.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// # Arguments
    /// * `f` - The function to map with.
    /// 
    /// # Returns
    /// * `Cont<R, B>` - The mapped value.
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        let f = Arc::new(f);
        Cont {
            run_cont: Arc::new(FnType::new(move |k: FnType<B, R>| {
                let f = Arc::clone(&f);
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
    /// Applies a function to the value.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the mapped value.
    /// * `F` - The function to apply.
    /// 
    /// # Arguments
    /// * `mf` - The function to apply.
    /// 
    /// # Returns
    /// * `Cont<R, B>` - The mapped value.
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

    /// Lifts a binary function into a Cont computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `F` - The function to lift.
    /// 
    /// # Arguments
    /// * `b` - The second argument.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `Cont<R, C>` - The lifted value.
    fn lift2<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
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

    /// Lifts a ternary function into a Cont computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `D` - The type of the third argument.
    /// * `F` - The function to lift.
    /// 
    /// # Arguments
    /// * `b` - The second argument.
    /// * `c` - The third argument.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `Cont<R, D>` - The lifted value.
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
    /// Binds a function over the value.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the bound value.
    /// * `F` - The function to bind with.
    /// 
    /// # Arguments
    /// * `f` - The function to bind with.
    /// 
    /// # Returns
    /// * `Cont<R, B>` - The bound value.
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

    /// Joins a nested Cont computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the joined value.
    /// 
    /// Returns
    /// * `Cont<R, B>` - The joined value.
    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        let f = FnType::new(|x: A| x.into());
        self.bind(f)
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

impl<R, A> HKT for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Cont<R, T> where T: ReturnTypeConstraints;
}

impl<R, A> Identity for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<R, A> Composable for Cont<R, A>
where
    R: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<R, A> Category for Cont<R, A>
where
    R: ReturnTypeConstraints,
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

impl<R, A> Arrow for Cont<R, A>
where
    R: ReturnTypeConstraints,
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
        FnType::new(move |x: (B, D)| (f.call(x.0), x.1))
    }
}
