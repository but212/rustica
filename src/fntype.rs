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
use crate::category::hkt::TypeConstraints;
use std::marker::PhantomData;

/// A function that is both Send and Sync
#[derive(Clone)]
pub struct FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    f: Arc<dyn Fn(I) -> O + Send + Sync>,
    _phantom: PhantomData<(I, O)>,
}

impl<I, O> FnTrait<I, O> for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn new<F: Fn(I) -> O + Send + Sync + 'static>(f: F) -> Self
    {
        FnType {
            f: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    fn call(&self, input: I) -> O {
        (self.f)(input)
    }
}

impl<I, O> PartialEq for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = I::default();
        self.call(test_value.clone()) == other.call(test_value)
    }
}

impl<I, O> Eq for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{}

impl<I, O> Default for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn default() -> Self {
        FnType::new(|_| O::default())
    }
}

impl<I, O> Debug for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FnType(<function>)")
    }
}

/// A trait for functions that are Send + Sync
pub trait FnTrait<A, B>: TypeConstraints
where
    A: TypeConstraints,
    B: TypeConstraints,
{
    fn new<F: Fn(A) -> B + Send + Sync + 'static>(f: F) -> Self;

    /// Call the function with the given argument
    fn call(&self, a: A) -> B;
}
