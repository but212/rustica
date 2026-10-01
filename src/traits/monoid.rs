#![doc = include_str!("../../docs/traits/monoid.md")]

use alloc::{string::String, vec::Vec};

use crate::traits::semigroup::Semigroup;

/// A [`Semigroup`] equipped with an identity element [`empty`](Monoid::empty).
///
/// # Laws
///
/// Implementations must satisfy identity laws alongside semigroup associativity:
///
/// ```text
/// x.combine(Self::empty()) == x           // Right identity
/// Self::empty().combine(x) == x           // Left identity
/// (a.combine(b)).combine(c) == a.combine(b.combine(c)) // Associativity
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
///
/// let hello = String::from("Hello");
/// assert_eq!(hello.clone().combine(String::empty()), hello);
/// ```
pub trait Monoid: Semigroup {
    /// Returns the identity element.
    ///
    /// Combining this element with any `x` yields `x`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let empty_string = String::empty();
    /// let hello = String::from("Hello");
    ///
    /// assert_eq!(hello.clone().combine(empty_string.clone()), hello.clone());
    /// assert_eq!(String::empty().combine(hello.clone()), hello.clone());
    /// ```
    fn empty() -> Self;
}

impl<T> Monoid for Vec<T> {
    fn empty() -> Self {
        Vec::new()
    }
}

impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
}

/// Combines an iterator of monoid values, returning [`Monoid::empty`] if empty.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
///
/// let strings = vec![String::from("Hello"), String::from(" "), String::from("World")];
/// assert_eq!(monoid::combine_all(strings), String::from("Hello World"));
///
/// let empty: Vec<String> = vec![];
/// assert_eq!(monoid::combine_all(empty), String::empty());
/// ```
#[inline]
pub fn combine_all<M, I>(values: I) -> M
where
    M: Monoid,
    I: IntoIterator<Item = M>,
{
    let mut iter = values.into_iter();
    match iter.next() {
        Some(first) => iter.fold(first, |acc, x| acc.combine(x)),
        None => M::empty(),
    }
}

/// Combines `value` with itself `n` times, returning [`Monoid::empty`] when `n == 0`.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
///
/// let hello = String::from("Hello");
/// assert_eq!(monoid::repeat(hello, 3), "HelloHelloHello");
///
/// let zero_repeat = monoid::repeat(String::from("World"), 0);
/// assert_eq!(zero_repeat, String::empty());
/// ```
#[inline]
pub fn repeat<M>(value: M, n: usize) -> M
where
    M: Monoid + Clone,
{
    core::iter::repeat_n(value, n)
        .reduce(|acc, x| acc.combine(x))
        .unwrap_or_else(M::empty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    struct CloneCounter {
        val: i32,
        clones: Arc<AtomicUsize>,
    }

    impl Clone for CloneCounter {
        fn clone(&self) -> Self {
            self.clones.fetch_add(1, Ordering::SeqCst);
            Self {
                val: self.val,
                clones: Arc::clone(&self.clones),
            }
        }
    }

    impl Semigroup for CloneCounter {
        fn combine(self, other: Self) -> Self {
            Self {
                val: self.val + other.val,
                clones: self.clones,
            }
        }
    }

    impl Monoid for CloneCounter {
        fn empty() -> Self {
            Self {
                val: 0,
                clones: Arc::new(AtomicUsize::new(0)),
            }
        }
    }

    #[test]
    fn test_repeat_clone_efficiency() {
        let counter = Arc::new(AtomicUsize::new(0));
        let item = CloneCounter {
            val: 5,
            clones: Arc::clone(&counter),
        };

        let res = repeat(item, 3);
        assert_eq!(res.val, 15);
        // For n = 3, optimal clone count is exactly 2 (n - 1).
        assert_eq!(counter.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn test_repeat_boundary_cases() {
        let counter = Arc::new(AtomicUsize::new(0));
        let make_item = |val| CloneCounter {
            val,
            clones: Arc::clone(&counter),
        };

        // n = 0: empty element, 0 clones
        let res0 = repeat(make_item(5), 0);
        assert_eq!(res0.val, 0);
        assert_eq!(counter.load(Ordering::SeqCst), 0);

        // n = 1: value itself, 0 clones
        let res1 = repeat(make_item(5), 1);
        assert_eq!(res1.val, 5);
        assert_eq!(counter.load(Ordering::SeqCst), 0);

        // n = 2: 1 clone
        let res2 = repeat(make_item(5), 2);
        assert_eq!(res2.val, 10);
        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }
}
