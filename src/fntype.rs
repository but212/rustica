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
use crate::traits::hkt::TypeConstraints;
use std::marker::PhantomData;
use futures::future::BoxFuture;

/// A function type that is both `Send` and `Sync`.
///
/// This struct wraps a function that can be safely shared between threads and
/// implements `Clone`. It uses `Arc` for thread-safe reference counting and
/// `PhantomData` to handle unused type parameters.
///
/// # Type Parameters
///
/// * `I`: The input type, which must satisfy `TypeConstraints`.
/// * `O`: The output type, which must satisfy `TypeConstraints`.
///
/// # Examples
///
/// ```
/// use rustica::fntype::{FnType, FnTrait};
/// use rustica::traits::hkt::TypeConstraints;
///
/// let add_one = FnType::new(|x: i32| x + 1);
/// assert_eq!(add_one.call(5), 6);
/// ```
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
    /// Creates a new `FnType` instance from a given function.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes an input of type `I` and returns an output of type `O`.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function, which must implement `Fn(I) -> O`, `Send`, `Sync`, and have a `'static` lifetime.
    ///
    /// # Returns
    ///
    /// Returns a new `FnType<I, O>` instance.
    fn new<F: Fn(I) -> O + Send + Sync + 'static>(f: F) -> Self {
        FnType {
            f: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    /// Calls the wrapped function with the given input.
    ///
    /// # Arguments
    ///
    /// * `input` - The input value of type `I`.
    ///
    /// # Returns
    ///
    /// Returns the output value of type `O`.
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
///
/// This trait defines a common interface for function types that are
/// both `Send` and `Sync`, allowing them to be safely shared and used
/// across threads.
///
/// # Type Parameters
///
/// * `A`: The input type of the function, must implement `TypeConstraints`
/// * `B`: The output type of the function, must implement `TypeConstraints`
///
/// # Examples
///
/// ```
/// use rustica::fntype::FnTrait;
/// use rustica::traits::hkt::TypeConstraints;
///
/// #[derive(Clone, Debug, PartialEq, Eq, Default)]
/// struct MyFn;
///
/// impl FnTrait<i32, String> for MyFn {
///     fn new<F: Fn(i32) -> String + Send + Sync + 'static>(f: F) -> Self {
///         // Implementation details...
///         MyFn
///     }
///
///     fn call(&self, a: i32) -> String {
///         // Implementation details...
///         format!("Input: {}", a)
///     }
/// }
/// ```
pub trait FnTrait<A, B>: TypeConstraints
where
    A: TypeConstraints,
    B: TypeConstraints,
{
    /// Creates a new instance of the function type.
    ///
    /// # Type Parameters
    ///
    /// * `F`: A function type that is `Fn(A) -> B`, `Send`, `Sync`, and `'static`
    ///
    /// # Arguments
    ///
    /// * `f`: The function to be wrapped
    fn new<F: Fn(A) -> B + Send + Sync + 'static>(f: F) -> Self;

    /// Calls the function with the given argument.
    ///
    /// # Arguments
    ///
    /// * `a`: The input value of type `A`
    ///
    /// # Returns
    ///
    /// The output value of type `B`
    fn call(&self, a: A) -> B;
}


#[derive(Clone)]
pub struct AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    f: Arc<dyn Fn(I) -> BoxFuture<'static, O> + Send + Sync>,
    _phantom: PhantomData<(I, O)>,
}

impl<I, O> AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(I) -> BoxFuture<'static, O> + Send + Sync + 'static,
    {
        AsyncFnType {
            f: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    pub async fn call(&self, input: I) -> O {
        (self.f)(input).await
    }
}

impl<I, O> PartialEq for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let test_value = I::default();
        futures::executor::block_on(self.call(test_value.clone())) == futures::executor::block_on(other.call(test_value))
    }
}

impl<I, O> Eq for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{}

impl<I, O> Default for AsyncFnType<I, O>
where
    I: TypeConstraints,
    O: TypeConstraints,
{
    fn default() -> Self {
        AsyncFnType::new(|_| Box::pin(async { O::default() }))
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