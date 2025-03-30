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

/// A thread-safe version of Memoize that can be safely shared across threads.
pub struct ThreadSafeMemoize<T> {
    f: Arc<dyn Fn() -> T + Send + Sync>,
    cache: Arc<Mutex<Option<T>>>,
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

    pub fn clear_cache(&self) {
        let mut cache = self.cache.borrow_mut();
        *cache = None;
    }

    pub fn get_ref(&self) -> impl std::ops::Deref<Target = T> + '_ {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some((self.f.borrow())());
        }
        std::cell::Ref::map(self.cache.borrow(), |opt| opt.as_ref().unwrap())
    }
}

impl<T> ThreadSafeMemoize<T> {
    pub fn new(f: impl Fn() -> T + Send + Sync + 'static) -> Self {
        ThreadSafeMemoize {
            f: Arc::new(f),
            cache: Arc::new(Mutex::new(None)),
        }
    }

    pub fn clear_cache(&self) {
        let mut cache = self.cache.lock().unwrap();
        *cache = None;
    }

    pub fn get_ref(&self) -> impl std::ops::Deref<Target = T> + '_ {
        struct RefWrapper<'a, T> {
            guard: std::sync::MutexGuard<'a, Option<T>>,
        }

        impl<'a, T> std::ops::Deref for RefWrapper<'a, T> {
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
