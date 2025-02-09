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
pub struct FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    f: Arc<dyn Fn(I) -> O + Send + Sync>,
    _phantom: PhantomData<(I, O)>,
}

impl<I, O> Debug for FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FnType(<function>)")
    }
}

impl<I, O> PartialEq for FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = I::default();
        self.call(test_value.clone()) == other.call(test_value)
    }
}

impl<I, O> Eq for FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{}

impl<I, O> Default for FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    fn default() -> Self {
        FnType {
            f: Arc::new(|_: I| O::default()),
            _phantom: PhantomData,
        }
    }
}

impl<I, O> FnType<I, O>
where
    I: ReturnTypeConstraints,
    O: ReturnTypeConstraints,
{
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + 'static,
    {
        FnType {
            f: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    pub fn call(&self, input: I) -> O {
        (self.f)(input)
    }
}

/// A trait for functions that are Send + Sync
pub trait FnTrait<A, B>: ReturnTypeConstraints
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    /// Call the function with the given argument
    fn call(&self, a: A) -> B;
}

impl<A, B> FnTrait<A, B> for FnType<A, B>
where
    A: ReturnTypeConstraints,
    B: ReturnTypeConstraints,
{
    fn call(&self, a: A) -> B {
        (self.f)(a)
    }
}

impl<A, B, F> FnTrait<A, B> for F
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
    f: FnType<T, M>,
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
            f: FnType::new(f),
        }
    }

    /// Applies the function to a value.
    pub fn apply(&self, x: T) -> M {
        self.f.call(x)
    }
}

/// A function that implements Debug
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct DebugFn<T: ReturnTypeConstraints>(FnType<T, T>);

impl<T: ReturnTypeConstraints> DebugFn<T> {
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<T, T>,
    {
        DebugFn(FnType::new(move |x: T| f.call(x)))
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