use crate::prelude::*;
use crate::category::semigroup::Semigroup;
use crate::fntype::MonoidFn;

/// A monoid is a semigroup with an identity element.
pub trait Monoid: Semigroup {
    /// The identity element of the monoid.
    ///
    /// # Returns
    /// The identity element of the monoid.
    fn empty() -> Self;
}

impl<T, M> PartialEq for MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{
    /// Checks if two `MonoidFn` instances are equal.
    ///
    /// # Parameters
    /// - `self`: The first `MonoidFn` instance.
    /// - `other`: The second `MonoidFn` instance.
    ///
    /// # Returns
    /// `true` if the two instances are equal, `false` otherwise.
    fn eq(&self, other: &Self) -> bool {
        let x = T::default();
        self.apply(x.clone()) == other.apply(x)
    }
}

impl<T, M> Eq for MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{}

impl<T, M> Semigroup for MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{
    /// Combines two `MonoidFn` instances.
    ///
    /// # Parameters
    /// - `self`: The first `MonoidFn` instance.
    /// - `other`: The second `MonoidFn` instance.
    ///
    /// # Returns
    /// A new `MonoidFn` instance that is the combination of the two instances.
    fn combine(self, other: Self) -> Self {
        MonoidFn::new(move |x: T| {
            let a = self.apply(x.clone());
            let b = other.apply(x);
            a.combine(b)
        })
    }
}

impl<T, M> Monoid for MonoidFn<T, M>
where
    T: ReturnTypeConstraints,
    M: Monoid,
{
    /// The identity element of the `MonoidFn`.
    ///
    /// # Returns
    /// A new `MonoidFn` instance that is the identity element.
    fn empty() -> Self {
        MonoidFn::new(|_| M::empty())
    }
}

/// A monoid for vectors.
impl<T> Monoid for Vec<T>
where
    T: ReturnTypeConstraints,
{
    /// The identity element of the vector monoid.
    ///
    /// # Returns
    /// An empty vector.
    fn empty() -> Self {
        Vec::new()
    }
}

/// A monoid for strings.
impl Monoid for String {
    /// The identity element of the string monoid.
    ///
    /// # Returns
    /// An empty string.
    fn empty() -> Self {
        String::new()
    }
}
