use std::fmt::Debug;
use crate::fntype::SendSyncFn;
use crate::prelude::*;

/// A lens that focuses on a field of a struct.
pub trait Lens<S, A>: ReturnTypeConstraints
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Gets the field value from the struct.
    fn get(&self, s: &S) -> A;

    /// Sets the field value in the struct.
    fn set(&self, s: S, a: A) -> S;

    /// Modifies the field value in the struct.
    fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(A) -> A + Send + Sync + 'static;
}

/// A lens that focuses on a field of a struct.
#[derive(Clone)]
pub struct FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Gets the field value from the struct.
    get: SendSyncFn<S, A>,
    /// Sets the field value in the struct.
    set: SendSyncFn<(S, A), S>,
}

impl<S, A> FieldLens<S, A>
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
        FieldLens {
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
}

impl<S, A> PartialEq for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = S::default();
        let test_value_ref = &test_value;
        let test_value_a = A::default();
        self.get.call(test_value_ref.clone()) == other.get.call(test_value_ref.clone()) &&
        self.set.call((test_value.clone(), test_value_a.clone())) == other.set.call((test_value, test_value_a))
    }
}

impl<S, A> Eq for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{}

impl<S, A> Debug for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FieldLens")
            .field("get", &"<function>")
            .field("set", &"<function>")
            .finish()
    }
}

impl<S, A> Default for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        FieldLens {
            get: SendSyncFn::new(|_s: S| A::default()),
            set: SendSyncFn::new(|_args: (S, A)| S::default()),
        }
    }
}

impl<S, A> Lens<S, A> for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn get(&self, s: &S) -> A {
        self.get.call(s.clone())
    }

    fn set(&self, s: S, a: A) -> S {
        self.set.call((s, a))
    }

    fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(A) -> A + Send + Sync + 'static,
    {
        let a = self.get(&s);
        let f = SendSyncFn::new(f);
        self.set(s, f.call(a))
    }
}

impl<S, A> HKT for FieldLens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = FieldLens<S, T> where T: ReturnTypeConstraints;
}

/// A composed lens that focuses on a field through another lens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedLens<S, A, B>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// The outer lens.
    l1: FieldLens<S, A>,
    /// The inner lens.
    l2: FieldLens<A, B>,
}

impl<S, A, B> ComposedLens<S, A, B>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// Creates a new composed lens.
    pub fn new(l1: FieldLens<S, A>, l2: FieldLens<A, B>) -> Self {
        ComposedLens { l1, l2 }
    }

    /// Gets the field value from the struct.
    pub fn get(&self, s: &S) -> B {
        let a = self.l1.get(s);
        self.l2.get(&a)
    }

    /// Sets the field value in the struct.
    pub fn set(&self, s: S, b: B) -> S {
        let a = self.l1.get(&s);
        let new_a = self.l2.set(a, b);
        self.l1.set(s, new_a)
    }

    /// Modifies the field value in the struct.
    pub fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(B) -> B + Send + Sync + 'static,
    {
        let a = self.l1.get(&s);
        let new_a = self.l2.modify(a, f);
        self.l1.set(s, new_a)
    }
}

impl<S, A, B> Default for ComposedLens<S, A, B>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    fn default() -> Self {
        ComposedLens {
            l1: FieldLens::default(),
            l2: FieldLens::default(),
        }
    }
}

impl<S, A, B> Lens<S, B> for ComposedLens<S, A, B>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    fn get(&self, s: &S) -> B {
        let a = self.l1.get(s);
        self.l2.get(&a)
    }

    fn set(&self, s: S, b: B) -> S {
        let a = self.l1.get(&s);
        let new_a = self.l2.set(a, b);
        self.l1.set(s, new_a)
    }

    fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(B) -> B + Send + Sync + 'static,
    {
        let a = self.l1.get(&s);
        let new_a = self.l2.modify(a, f);
        self.l1.set(s, new_a)
    }
}

impl<S, A, B> HKT for ComposedLens<S, A, B>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    type Output<T> = ComposedLens<S, A, T> where T: ReturnTypeConstraints;
}
