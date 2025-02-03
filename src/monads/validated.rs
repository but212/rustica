use std::fmt::Debug;
use std::hash::Hash;

use crate::category::{Applicative, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, BindFn, MonadFn};

pub trait ValidatedTypeConstraints: ReturnTypeConstraints + Extend<Self> + IntoIterator<Item = Self> {}

/// A type that represents a value that can be either valid or invalid
///
/// # Type Parameters
/// * `E` - The error type, must be a collection type that can extend itself
/// * `A` - The valid value type
///
/// # Laws
/// A Validated instance must satisfy these laws:
/// 1. Identity: `validated.map(|x| x) = validated`
/// 2. Composition: `validated.map(f).map(g) = validated.map(|x| g(f(x)))`
/// 3. Pure: `Validated::pure(x).map(f) = Validated::pure(f(x))`
/// 4. Applicative: Errors are accumulated when combining multiple Validated values
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    Valid(A),
    Invalid(Vec<E>),
}

impl<E, A> Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new valid value
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid value
    pub fn invalid(e: E) -> Self {
        let mut errors = Vec::new();
        errors.extend(std::iter::once(e));
        Validated::Invalid(errors)
    }

    /// Creates a new invalid value from a vector of errors
    pub fn invalid_vec(errors: Vec<E>) -> Self {
        Validated::Invalid(errors)
    }

    /// Maps a function over the valid value
    pub fn map_valid<B, F>(self, f: F) -> Validated<E, B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f.call(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    /// Maps a function over the invalid value
    pub fn map_invalid<G, F>(self, f: F) -> Validated<G, A>
    where
        G: ValidatedTypeConstraints,
        F: SendSyncFnTrait<E, G>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let mut errors = Vec::new();
                for e in es {
                    errors.extend(std::iter::once(f.call(e)));
                }
                Validated::Invalid(errors)
            }
        }
    }

    /// Combines two validated values using a function
    pub fn combine<B, C, F>(self, other: Validated<E, B>, f: F) -> Validated<E, C>
    where
        F: SendSyncFnTrait<A, SendSyncFn<B, C>>,
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        E: ValidatedTypeConstraints,
    {
        match (self, other) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call(a).call(b)),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
            (Validated::Invalid(e), _) | (_, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }

    /// Converts to a Result
    pub fn to_result(self) -> Result<A, Vec<E>> {
        match self {
            Validated::Valid(x) => Ok(x),
            Validated::Invalid(e) => Err(e),
        }
    }

    /// Creates from a Result
    pub fn from_result(result: Result<A, E>) -> Self {
        match result {
            Ok(x) => Validated::Valid(x),
            Err(e) => Validated::Invalid(vec![e]),
        }
    }
}

impl<E, A> Default for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        Validated::Invalid(Default::default())
    }
}

impl<E, A> HKT for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Validated<E, T> where T: ReturnTypeConstraints;
}

impl<E, A> Pure<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(x: A) -> Self::Output<A> {
        Validated::Valid(x)
    }
}

impl<E, A> Functor<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Validated<E, B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        self.map_valid(f)
    }
}

impl<E, A> Applicative<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, rf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ReturnTypeConstraints + ApplyFn<A, B>,
    {
        match (self, rf) {
            (Validated::Valid(x), Validated::Valid(f)) => Validated::Valid(f.call(x)),
            (Validated::Invalid(e1), Validated::Valid(_)) | (Validated::Valid(_), Validated::Invalid(e1)) => Validated::Invalid(e1),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        match (self, mb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call(a).call(b)),
            (Validated::Invalid(e1), Validated::Valid(_)) => Validated::Invalid(e1),
            (Validated::Valid(_), Validated::Invalid(e2)) => Validated::Invalid(e2),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
        }
    }

    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        match (self, mb, mc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f.call(a).call(b).call(c))
            }
            (Validated::Invalid(mut e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                e1.extend(e2);
                e1.extend(e3);
                Validated::Invalid(e1)
            }
            (Validated::Invalid(e), _, _) => Validated::Invalid(e),
            (_, Validated::Invalid(e), _) => Validated::Invalid(e),
            (_, _, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }
}

impl<E, A> Monad<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: BindFn<A, B, Self::Output<B>>,
    {
        match self {
            Validated::Valid(x) => f.call(x),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        A: Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(x) => x.into(),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>,
    {
        SendSyncFn::new(move |x: A| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}