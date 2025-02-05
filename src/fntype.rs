//! Function type definitions and wrappers for the rustica library.
//!
//! This module provides various function type definitions and wrappers that are used
//! throughout the library to ensure proper type safety, thread safety, and debugging
//! capabilities. It includes:
//!
//! - Send + Sync function wrappers
//! - Async function types
//! - Function types for monadic operations
//! - Function types for applicative operations
//! - Function types for contravariant functor operations
//! - Function types for comonadic operations

use std::sync::Arc;
use futures::future::BoxFuture;
use crate::category::hkt::ReturnTypeConstraints;
use crate::category::monoid::Monoid;
use std::fmt::Debug;
use std::marker::PhantomData;

/// A function that is both Send and Sync
#[derive(Clone)]
pub struct SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    f: Arc<dyn Fn(I) -> O + Send + Sync>,
    _phantom: PhantomData<(I, O)>,
}

impl<I, O> Debug for SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SendSyncFn(<function>)")
    }
}

impl<I, O> PartialEq for SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = I::default();
        self.call(test_value.clone()) == other.call(test_value)
    }
}

impl<I, O> Eq for SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{}

impl<I, O> Default for SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn default() -> Self {
        SendSyncFn {
            f: Arc::new(|_: I| O::default()),
            _phantom: PhantomData,
        }
    }
}

impl<I, O> SendSyncFn<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + 'static,
    {
        SendSyncFn {
            f: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    pub fn call(&self, input: I) -> O {
        (self.f)(input)
    }
}

/// A trait for functions that are Send + Sync
pub trait SendSyncFnTrait<A, B>: ReturnTypeConstraints
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// Call the function with the given argument
    fn call(&self, a: A) -> B;
}

impl<A, B> SendSyncFnTrait<A, B> for SendSyncFn<A, B>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    fn call(&self, a: A) -> B {
        (self.f)(a)
    }
}

impl<A, B, F> SendSyncFnTrait<A, B> for F
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    F: Fn(A) -> B + ReturnTypeConstraints,
{
    fn call(&self, a: A) -> B {
        self(a)
    }
}

/// A monoid for functions that return a monoid.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{
    /// The function.
    f: SendSyncFn<T, M>,
}

impl<T, M> MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{
    /// Creates a new monoid function.
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(T) -> M + Send + Sync + 'static,
    {
        MonoidFn {
            f: SendSyncFn::new(f),
        }
    }

    /// Applies the function to a value.
    pub fn apply(&self, x: T) -> M {
        self.f.call(x)
    }
}

/// A function that implements Debug
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct DebugFn<T: ReturnTypeConstraints>(SendSyncFn<T, T>);

impl<T: ReturnTypeConstraints> DebugFn<T> {
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<T, T>,
    {

        DebugFn(SendSyncFn::new(move |a| f.call(a)))
    }
}

/// A trait for functions that return a BoxFuture
pub trait AsyncFn<A, B>: ReturnTypeConstraints {
    /// Call the function with the given argument
    fn call(&self, a: A) -> BoxFuture<'static, B>;
}

impl<A, B, F> AsyncFn<A, B> for F
where
    F: Fn(A) -> BoxFuture<'static, B> + ReturnTypeConstraints,
{
    fn call(&self, a: A) -> BoxFuture<'static, B> {
        self(a)
    }
}

/// A trait for functions that can be used in bind operations
pub trait BindFn<A, B, M>: SendSyncFnTrait<A, M> + PartialEq
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    M: ReturnTypeConstraints,
{}

impl<T, A, B, M> BindFn<A, B, M> for T
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    M: ReturnTypeConstraints,
    T: SendSyncFnTrait<A, M>,
{}

/// A trait for functions that can be used in monadic operations
pub trait MonadFn<A, B, M>: SendSyncFnTrait<A, M> + Eq
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    M: ReturnTypeConstraints,
{}

impl<T, A, B, M> MonadFn<A, B, M> for T
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    M: ReturnTypeConstraints,
    T: SendSyncFnTrait<A, M>,
{}

/// A trait for functions that can be used in apply operations
pub trait ApplyFn<A, B>: SendSyncFnTrait<A, B>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{}

impl<T, A, B> ApplyFn<A, B> for T
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    T: SendSyncFnTrait<A, B>,
{}

/// A trait for functions that can be used in extend operations
pub trait ExtendFn<A, B, W>: SendSyncFnTrait<A, W>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    W: ReturnTypeConstraints,
{}

impl<T, A, B, W> ExtendFn<A, B, W> for T
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
    W: ReturnTypeConstraints,
    T: SendSyncFnTrait<A, W>,
{}

/// A trait for functions that can be used in contravariant functor operations
pub trait ContravariantFn<T, U>: SendSyncFnTrait<T, U>
where
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
{}

impl<F, T, U> ContravariantFn<T, U> for F
where
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
    F: SendSyncFnTrait<T, U>,
{}