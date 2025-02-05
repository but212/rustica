use std::fmt::Debug;
use crate::fntype::SendSyncFn;
use crate::prelude::*;

/// A lens that focuses on a field of a struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    get: SendSyncFn<S, A>,
    set: SendSyncFn<(S, A), S>,
}

impl<S, A> Lens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new lens.
    pub fn new<G, H>(get: G, set: H) -> Self
    where
        G: Fn(S) -> A + Send + Sync + 'static,
        H: Fn(S, A) -> S + Send + Sync + 'static,
    {
        Lens {
            get: SendSyncFn::new(get),
            set: SendSyncFn::new(move |args: (S, A)| set(args.0, args.1)),
        }
    }

    /// Gets the field value from the struct.
    pub fn get(&self, s: &S) -> A {
        self.get.call(s.clone())
    }

    /// Sets the field value in the struct.
    pub fn set(&self, s: S, a: A) -> S {
        self.set.call((s, a))
    }

    /// Modifies the field value in the struct.
    pub fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(A) -> A + Send + Sync + 'static,
    {
        let a = self.get(&s);
        let f = SendSyncFn::new(f);
        self.set(s, f.call(a))
    }

    /// Composes this lens with another lens.
    pub fn compose<B>(self, other: Lens<A, B>) -> Lens<S, B>
    where
        B: ReturnTypeConstraints,
    {
        Lens::new(
            {
                let self_clone = self.clone();
                let other_clone = other.clone();
                move |s: S| other_clone.get(&self_clone.get(&s))
            },
            {
                let self_clone = self.clone();
                let other_clone = other.clone();
                move |s: S, b: B| {
                    let a = self_clone.get(&s);
                    self_clone.set(s, other_clone.set(a, b))
                }
            },
        )
    }



    /// Creates a lens for a field.
    pub fn field<B>(get: impl Fn(A) -> B + Send + Sync + 'static, set: impl Fn(A, B) -> A + Send + Sync + 'static) -> Lens<A, B>
    where
        B: ReturnTypeConstraints,
    {
        Lens::new(get, set)
    }
}
