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
use crate::prelude::*;
use std::marker::PhantomData;
use futures::future::BoxFuture;

/// A trait for function types that can be called with a single argument
pub trait FnTrait<I, O>: HKT + TypeConstraints
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    /// Create a new function type instance
    fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + Clone + 'static;

    /// Call the function with the given input
    fn call(&self, input: I) -> O;

    /// Compose this function with another function
    fn compose<U, F>(self, f: F) -> FnType<I, U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        FnType::new_internal(move |x| f.call(self.call(x)))
    }

    /// Map over the output of this function
    fn map<U, F>(self, f: F) -> FnType<I, U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        self.compose(f)
    }
}

/// A trait for internal function type operations
pub trait FnTypeInternal<I, O>: HKT + TypeConstraints
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    type CallOutput;

    /// Create a new function type instance internally
    fn new_internal<F>(f: F) -> Self
    where
        F: Fn(I) -> Self::CallOutput + Send + Sync + 'static;

    /// Call the function with the given input
    fn call_internal(&self, input: I) -> Self::CallOutput;
}

/// A newtype wrapper for function types
#[derive(Clone)]
pub struct FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    f: Arc<dyn Fn(I) -> O + Send + Sync>,
    _marker: PhantomData<(I, O)>,
}

impl<I, O> FnTypeInternal<I, O> for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    type CallOutput = O;

    fn new_internal<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + 'static,
    {
        FnType {
            f: Arc::new(f),
            _marker: PhantomData,
        }
    }

    fn call_internal(&self, input: I) -> O {
        (self.f)(input)
    }
}

impl<I, O> FnTrait<I, O> for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + Clone + 'static,
    {
        Self::new_internal(f)
    }

    fn call(&self, input: I) -> O {
        self.call_internal(input)
    }
}

/// A newtype wrapper for async function types
#[derive(Clone)]
pub struct AsyncFnType<I: TypeConstraints, O: TypeConstraints> {
    f: Arc<dyn Fn(I) -> BoxFuture<'static, O> + Send + Sync>,
    _marker: PhantomData<(I, O)>,
}

impl<I: TypeConstraints, O: TypeConstraints> AsyncFnType<I, O> {
    /// Call the async function and await its result
    pub async fn call_async(&self, input: I) -> O {
        (self.f)(input).await
    }
}

impl<I: TypeConstraints, O: TypeConstraints> FnTypeInternal<I, O> for AsyncFnType<I, O> {
    type CallOutput = O;

    fn new_internal<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        AsyncFnType {
            f: Arc::new(move |x| {
                let f = Arc::clone(&f);
                Box::pin(async move { f(x) })
            }),
            _marker: PhantomData,
        }
    }

    fn call_internal(&self, input: I) -> O {
        futures::executor::block_on(self.call_async(input))
    }
}

impl<I: TypeConstraints, O: TypeConstraints> FnTrait<I, O> for AsyncFnType<I, O> {
    fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> O + Send + Sync + Clone + 'static,
    {
        Self::new_internal(f)
    }

    fn call(&self, input: I) -> O {
        self.call_internal(input)
    }
}

impl<I: TypeConstraints, O: TypeConstraints> Identity<O> for AsyncFnType<I, O> {
    fn identity() -> Self::Output<O> {
        AsyncFnType::new(|_i: I| O::default())
    }

    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        AsyncFnType::new(move |_i: I| f.call(O::default()))
    }
}

impl<I: TypeConstraints, O: TypeConstraints> Composable<O> for FnType<I, O> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        self.compose(f)
    }
}

impl<I: TypeConstraints, O: TypeConstraints> Identity<O> for FnType<I, O> {
    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        FnType::new(move |_i: I| f.call(O::default()))
    }
}

impl<I, O> Default for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints + Default,
{
    fn default() -> Self {
        AsyncFnType::new(|_| O::default())
    }
}

impl<I, O> Debug for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FnType")
            .field("type", &format!("Fn({}) -> {}", std::any::type_name::<I>(), std::any::type_name::<O>()))
            .finish()
    }
}

impl<I, O> Default for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn default() -> Self {
        FnType::new_internal(|_| O::default())
    }
}

impl<I, O> PartialEq for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}

impl<I, O> Eq for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
}

impl<I, O> HKT for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    type Output<U> = FnType<I, U> where U: TypeConstraints;
}

impl<I, O> Functor<O> for FnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints + Identity<O>,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        self.map(f)
    }

    fn lift<U, F>(f: F) -> FnType<Self, Self::Output<U>>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        FnType::new_internal(move |g: Self| g.map(f.clone()))
    }
}

impl<I, O> Debug for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AsyncFnType(<function>)")
    }
}

impl<I, O> HKT for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    type Output<U> = AsyncFnType<I, U> where U: TypeConstraints;
}

impl<I, O> PartialEq for AsyncFnType<I, O>
where
    I: TypeConstraints + Clone,
    O: TypeConstraints + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = I::default();
        futures::executor::block_on(self.call_async(test_value.clone())) == 
        futures::executor::block_on(other.call_async(test_value))
    }
}

impl<I, O> Eq for AsyncFnType<I, O>
where
    I: TypeConstraints + Clone,
    O: TypeConstraints + Eq,
{
}

impl<I, O> Composable<O> for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<O, U>,
    {
        AsyncFnType::new(move |x| f.call(self.call_internal(x)))
    }
}