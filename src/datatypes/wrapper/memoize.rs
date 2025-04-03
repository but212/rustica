//! # Memoize
//!
//! This module provides the `Memoize` wrapper type that caches the result of a function call.
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoize::Memoize;
//! use rustica::traits::evaluate::Evaluate;
//! use std::sync::atomic::{AtomicUsize, Ordering};
//!
//! // Track number of evaluations
//! static COUNTER: AtomicUsize = AtomicUsize::new(0);
//!
//! // Create a memoized function
//! let expensive_fn = || {
//!     COUNTER.fetch_add(1, Ordering::SeqCst);
//!     42
//! };
//!
//! let memoized = Memoize::new(expensive_fn);
//!
//! // First call computes the value
//! assert_eq!(memoized.evaluate(), 42);
//! assert_eq!(COUNTER.load(Ordering::SeqCst), 1);
//!
//! // Second call returns cached value
//! assert_eq!(memoized.evaluate(), 42);
//! assert_eq!(COUNTER.load(Ordering::SeqCst), 1);
//! ```
use crate::traits::evaluate::Evaluate;
use crate::traits::hkt::HKT;
use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

/// A wrapper that memoizes (caches) the result of a function.
///
/// This wrapper evaluates the inner function only once and caches the result
/// for subsequent evaluations, improving performance for expensive computations.
///
/// # Type Parameters
///
/// * `F` - The function type that produces values of type `T`
/// * `T` - The type of value produced by the function
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::memoize::Memoize;
/// use rustica::traits::evaluate::Evaluate;
///
/// // Create an expensive computation
/// let expensive_computation = || {
///     println!("Computing...");
///     (1..1000).sum::<i32>()
/// };
///
/// // Wrap it in Memoize
/// let memoized = Memoize::new(expensive_computation);
///
/// // First call computes and caches
/// let result1 = memoized.evaluate();
/// // Second call uses cached value
/// let result2 = memoized.evaluate();
///
/// assert_eq!(result1, result2);
/// // "Computing..." is printed only once
/// ```
pub struct Memoize<T> {
    f: Rc<RefCell<dyn Fn() -> T>>,
    cache: Rc<RefCell<Option<T>>>,
}

/// A wrapper that memoizes (caches) the result of a function that takes an input.
///
/// This wrapper evaluates the inner function only once for a given input and caches the result
/// for subsequent calls with the same input, improving performance for expensive computations.
///
/// # Type Parameters
///
/// * `I` - The input type for the function
/// * `O` - The output type produced by the function
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::memoize::MemoizeFn;
/// use std::cell::RefCell;
/// use std::rc::Rc;
///
/// // Create a memoized function
/// let memoized = MemoizeFn::new(|x: i32| {
///     println!("Computing for {}", x);
///     x * x
/// });
///
/// // First call computes and caches
/// let result1 = memoized.clone().call(5);
/// // Second call with same input uses cached value
/// let result2 = memoized.call(5);
///
/// assert_eq!(result1, result2);
/// // "Computing for 5" is printed only once
/// ```
#[derive(Clone)]
pub struct MemoizeFn<I, O> {
    f: Rc<RefCell<dyn Fn(I) -> O>>,
    cache: Rc<RefCell<Option<O>>>,
}

/// A thread-safe version of Memoize that can be safely shared across threads.
///
/// This wrapper evaluates the inner function only once and caches the result
/// for subsequent evaluations, even when accessed from multiple threads.
///
/// # Type Parameters
///
/// * `T` - The type of value produced by the function
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::memoize::ThreadSafeMemoize;
/// use rustica::traits::evaluate::Evaluate;
/// use std::sync::Arc;
/// use std::thread;
///
/// // Create a memoized computation
/// let memoized = ThreadSafeMemoize::new(|| {
///     println!("Computing expensive result...");
///     42
/// });
///
/// // Share across threads
/// let handles: Vec<_> = (0..5).map(|_| {
///     let memo = memoized.clone();
///     thread::spawn(move || {
///         memo.evaluate()
///     })
/// }).collect();
///
/// // All threads get the same result, but computation happens only once
/// for handle in handles {
///     assert_eq!(handle.join().unwrap(), 42);
/// }
/// ```
#[derive(Clone)]
pub struct ThreadSafeMemoize<T> {
    f: Arc<dyn Fn() -> T + Send + Sync>,
    cache: Arc<Mutex<Option<T>>>,
}

/// A wrapper that memoizes (caches) the result of a function that takes an input.
///
/// This wrapper evaluates the inner function only once for a given input and caches the result
/// for subsequent calls with the same input, even when accessed from multiple threads.
///
/// # Type Parameters
///
/// * `I` - The input type for the function
/// * `O` - The output type produced by the function
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::memoize::ThreadSafeMemoizeFn;
/// use std::sync::Arc;
/// use std::thread;
///
/// // Create a thread-safe memoized function
/// let memoized = ThreadSafeMemoizeFn::new(|x: i32| {
///     println!("Computing for {}", x);
///     x * x
/// });
///
/// // Share across threads with same input
/// let handles: Vec<_> = (0..5).map(|_| {
///     let memo = memoized.clone();
///     thread::spawn(move || {
///         memo.call(5)
///     })
/// }).collect();
///
/// // All threads get the same result, computation happens only once
/// for handle in handles {
///     assert_eq!(handle.join().unwrap(), 25);
/// }
/// ```
#[derive(Clone)]
pub struct ThreadSafeMemoizeFn<I, O> {
    f: Arc<dyn Fn(I) -> O + Send + Sync>,
    cache: Arc<Mutex<Option<O>>>,
}

impl<T> Memoize<T> {
    /// Creates a new memoized function wrapper.
    ///
    /// # Parameters
    ///
    /// * `f` - The function to memoize
    pub fn new(f: impl Fn() -> T + 'static) -> Self {
        Memoize {
            f: Rc::new(RefCell::new(f)),
            cache: Rc::new(RefCell::new(None)),
        }
    }

    /// Clears the cached result, forcing the next evaluation to recompute.
    ///
    /// This method resets the internal cache to `None`, which means the next
    /// call to `evaluate` or `get_ref` will execute the wrapped function again.
    pub fn clear_cache(&self) {
        let mut cache = self.cache.borrow_mut();
        *cache = None;
    }

    /// Returns a reference to the cached result, computing it if necessary.
    ///
    /// This method provides access to the cached value without cloning it,
    /// which can be more efficient for large data structures.
    ///
    /// # Returns
    ///
    /// A smart pointer that implements `Deref<Target = T>`, allowing read-only
    /// access to the cached value.
    pub fn get_ref(&self) -> impl std::ops::Deref<Target = T> + '_ {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some((self.f.borrow())());
        }
        std::cell::Ref::map(self.cache.borrow(), |opt| opt.as_ref().unwrap())
    }
}

impl<I, O> MemoizeFn<I, O> {
    /// Creates a new memoized function wrapper for a function with an input parameter.
    ///
    /// # Parameters
    ///
    /// * `f` - The function to memoize
    pub fn new(f: impl Fn(I) -> O + 'static) -> Self {
        MemoizeFn {
            f: Rc::new(RefCell::new(f)),
            cache: Rc::new(RefCell::new(None)),
        }
    }

    /// Clears the cached result, forcing the next evaluation to recompute.
    pub fn clear_cache(&self) {
        let mut cache = self.cache.borrow_mut();
        *cache = None;
    }

    /// Returns a reference to the cached result, computing it if necessary.
    ///
    /// # Parameters
    ///
    /// * `input` - The input to pass to the function
    pub fn get_ref(&self, input: I) -> impl std::ops::Deref<Target = O> + '_ {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some((self.f.borrow())(input));
        }
        std::cell::Ref::map(self.cache.borrow(), |opt| opt.as_ref().unwrap())
    }

    /// Calls the function with the given input, using the cached result if available.
    ///
    /// # Parameters
    ///
    /// * `input` - The input to pass to the function
    ///
    /// # Returns
    ///
    /// The result of the function call, either computed or retrieved from cache
    pub fn call(&self, input: I) -> O
    where
        O: Clone,
    {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some((self.f.borrow())(input));
        }
        cache.as_ref().unwrap().clone()
    }
}

impl<T> ThreadSafeMemoize<T> {
    /// Creates a new thread-safe memoized function wrapper.
    ///
    /// # Parameters
    ///
    /// * `f` - The function to memoize, must implement Send + Sync
    ///
    /// # Returns
    ///
    /// A new ThreadSafeMemoize instance that wraps the provided function
    pub fn new(f: impl Fn() -> T + Send + Sync + 'static) -> Self {
        ThreadSafeMemoize {
            f: Arc::new(f),
            cache: Arc::new(Mutex::new(None)),
        }
    }

    /// Clears the cached result, forcing the next evaluation to recompute.
    ///
    /// This method resets the internal cache to `None`, which means the next
    /// call to `evaluate` or `get_ref` will execute the wrapped function again.
    pub fn clear_cache(&self) {
        let mut cache = self.cache.lock().unwrap();
        *cache = None;
    }

    /// Returns a reference to the cached result, computing it if necessary.
    ///
    /// This method provides access to the cached value without cloning it,
    /// which can be more efficient for large data structures.
    ///
    /// # Returns
    ///
    /// A smart pointer that implements `Deref<Target = T>`, allowing read-only
    /// access to the cached value.
    pub fn get_ref(&self) -> impl std::ops::Deref<Target = T> + '_ {
        struct RefWrapper<'a, T> {
            guard: std::sync::MutexGuard<'a, Option<T>>,
        }

        impl<T> std::ops::Deref for RefWrapper<'_, T> {
            type Target = T;
            fn deref(&self) -> &Self::Target {
                self.guard.as_ref().unwrap()
            }
        }

        let mut guard = self.cache.lock().unwrap();
        if guard.is_none() {
            *guard = Some((self.f)());
        }

        RefWrapper { guard }
    }
}

impl<I, O> ThreadSafeMemoizeFn<I, O> {
    /// Creates a new thread-safe memoized function wrapper for a function with an input parameter.
    ///
    /// # Parameters
    ///
    /// * `f` - The function to memoize, must implement Send + Sync
    ///
    /// # Returns
    ///
    /// A new ThreadSafeMemoizeFn instance that wraps the provided function
    pub fn new(f: impl Fn(I) -> O + Send + Sync + 'static) -> Self {
        ThreadSafeMemoizeFn {
            f: Arc::new(f),
            cache: Arc::new(Mutex::new(None)),
        }
    }

    /// Clears the cached result, forcing the next evaluation to recompute.
    ///
    /// This method resets the internal cache to `None`, which means the next
    /// call to `evaluate` or `get_ref` will execute the wrapped function again.
    pub fn clear_cache(&self) {
        let mut cache = self.cache.lock().unwrap();
        *cache = None;
    }

    /// Returns a reference to the cached result, computing it if necessary.
    ///
    /// This method provides thread-safe access to the cached value without cloning it,
    /// which can be more efficient for large data structures.
    ///
    /// # Parameters
    ///
    /// * `input` - The input to pass to the function
    ///
    /// # Returns
    ///
    /// A smart pointer that implements `Deref<Target = O>`, allowing read-only
    /// access to the cached value.
    pub fn get_ref(&self, input: I) -> impl std::ops::Deref<Target = O> + '_ {
        struct RefWrapper<'a, T> {
            guard: std::sync::MutexGuard<'a, Option<T>>,
        }

        impl<T> std::ops::Deref for RefWrapper<'_, T> {
            type Target = T;
            fn deref(&self) -> &Self::Target {
                self.guard.as_ref().unwrap()
            }
        }

        let mut guard = self.cache.lock().unwrap();
        if guard.is_none() {
            *guard = Some((self.f)(input));
        }

        RefWrapper { guard }
    }

    /// Calls the function with the given input, using the cached result if available.
    ///
    /// This method provides thread-safe memoization, ensuring the function is only
    /// executed once even when called from multiple threads.
    ///
    /// # Parameters
    ///
    /// * `input` - The input to pass to the function
    ///
    /// # Returns
    ///
    /// The result of the function call, either computed or retrieved from cache
    pub fn call(&self, input: I) -> O
    where
        O: Clone,
    {
        let mut guard = self.cache.lock().unwrap();
        if guard.is_none() {
            *guard = Some((self.f)(input));
        }
        guard.as_ref().unwrap().clone()
    }
}

impl<T> HKT for Memoize<T> {
    type Source = T;
    type Output<U> = Memoize<U>;
}

impl<T> HKT for ThreadSafeMemoize<T> {
    type Source = T;
    type Output<U> = ThreadSafeMemoize<U>;
}

impl<T> Evaluate for Memoize<T>
where
    T: Clone,
{
    #[inline]
    fn evaluate(&self) -> Self::Source {
        let mut cache = self.cache.borrow_mut();
        if let Some(ref cached) = *cache {
            cached.clone()
        } else {
            let result = (self.f.borrow())();
            *cache = Some(result.clone());
            result
        }
    }

    fn evaluate_owned(self) -> Self::Source
    where
        Self::Source: Clone,
    {
        let mut cache = self.cache.borrow_mut();
        if let Some(cached) = &*cache {
            cached.clone()
        } else {
            let result = (self.f.borrow())();
            *cache = Some(result.clone());
            result
        }
    }
}

impl<T> Evaluate for ThreadSafeMemoize<T>
where
    T: Clone,
{
    #[inline]
    fn evaluate(&self) -> Self::Source {
        let mut cache = self.cache.lock().unwrap();
        if let Some(ref cached) = *cache {
            cached.clone()
        } else {
            let result = (self.f)();
            *cache = Some(result.clone());
            result
        }
    }

    fn evaluate_owned(self) -> Self::Source
    where
        Self::Source: Clone,
    {
        let mut cache = self.cache.lock().unwrap();
        if let Some(cached) = &*cache {
            cached.clone()
        } else {
            let result = (self.f)();
            *cache = Some(result.clone());
            result
        }
    }
}

impl<T> fmt::Debug for Memoize<T>
where
    T: Clone + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cache = self.cache.borrow();
        if let Some(ref cached) = *cache {
            write!(f, "Memoize(cached: {:?})", cached)
        } else {
            write!(f, "Memoize(not cached)")
        }
    }
}

impl<T> fmt::Debug for ThreadSafeMemoize<T>
where
    T: Clone + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cache = self.cache.lock().unwrap();
        if let Some(ref cached) = *cache {
            write!(f, "ThreadSafeMemoize(cached: {:?})", cached)
        } else {
            write!(f, "ThreadSafeMemoize(not cached)")
        }
    }
}
