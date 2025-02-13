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

use std::{fmt::Debug, sync::Arc};
use crate::category::hkt::ReturnTypeConstraints;
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
        FnType::new(|_| O::default())
    }
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