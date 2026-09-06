//! # Thunk
//!
//! Deprecated in 0.15.0: Use standard closures (`impl FnOnce() -> T`) or lazy initialization instead.

use std::marker::PhantomData;

use crate::traits::hkt::HKT;

/// A thunk that lazily produces a value when evaluated.
#[deprecated(
    since = "0.15.0",
    note = "use standard closures (`impl FnOnce() -> T`) or lazy initialization instead"
)]
#[derive(Clone)]
pub struct Thunk<F, T>
where
    F: Fn() -> T,
{
    function: F,
    _phantom: PhantomData<T>,
}

#[allow(deprecated)]
impl<F, T> Thunk<F, T>
where
    F: Fn() -> T,
{
    /// Creates a new thunk from a function.
    #[inline]
    pub fn new(f: F) -> Self {
        Thunk {
            function: f,
            _phantom: PhantomData,
        }
    }

    /// Evaluates the thunk by executing the wrapped function.
    #[inline]
    pub fn evaluate(&self) -> T {
        (self.function)()
    }

    /// Evaluates the thunk, consuming it.
    #[inline]
    pub fn evaluate_owned(self) -> T {
        (self.function)()
    }
}

#[allow(deprecated)]
impl<F, T> HKT for Thunk<F, T>
where
    F: Fn() -> T,
{
    type Source = T;
    type Output<U> = Thunk<Box<dyn Fn() -> U>, U>;
}

#[cfg(test)]
mod tests {
    #[allow(deprecated)]
    use super::Thunk;

    #[test]
    fn thunk_evaluates_lazily() {
        #[allow(deprecated)]
        let thunk = Thunk::new(|| 42);
        assert_eq!(thunk.evaluate(), 42);
        assert_eq!(thunk.evaluate_owned(), 42);
    }
}
