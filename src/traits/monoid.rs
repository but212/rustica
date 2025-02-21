use crate::traits::hkt::TypeConstraints;
use crate::traits::semigroup::Semigroup;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A trait for monoids, which are semigroups with an identity element.
/// 
/// Monoids extend semigroups by introducing an identity element, often called
/// the "empty" element. This element, when combined with any other element,
/// leaves that element unchanged.
/// 
/// # Type Parameters
/// 
/// * `T` - The type of elements in the monoid
/// 
/// # Laws
/// 
/// A Monoid instance must satisfy these laws:
/// 
/// 1. Identity: For any value `x`,
///    `x.combine(empty()) = x = empty().combine(x)`
/// 2. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = (x.combine(y)).combine(z)`
/// 3. Empty Uniqueness: For any monoid `M`,
///    `exists unique e: e.combine(x) = x = x.combine(e)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.combine(y)) = η(x).combine(η(y))`
/// 5. Empty Preservation: For any natural transformation `η`,
///    `η(empty()) = empty()`
pub trait Monoid<T>: Semigroup<T>
where
    T: TypeConstraints,
{
    /// Returns the identity element of the monoid.
    ///
    /// The identity element is a value that, when combined with any other element,
    /// leaves that element unchanged. This method should be implemented to return
    /// the unique identity element for the monoid.
    ///
    /// # Returns
    ///
    /// The identity element of the monoid.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// struct AdditiveInt(i32);
    /// 
    /// impl Semigroup<i32> for AdditiveInt {
    ///     fn combine(self, other: Self) -> Self {
    ///         AdditiveInt(self.0 + other.0)
    ///     }
    /// }
    ///
    /// impl Monoid<i32> for AdditiveInt {
    ///     fn empty() -> Self {
    ///         AdditiveInt(0)  // 0 is the identity for addition
    ///     }
    /// }
    /// ```
    fn empty() -> Self;

    /// Combines all elements in an iterator using the monoid's operation.
    ///
    /// This method combines all elements in the given iterator using the monoid's
    /// combine operation. If the iterator is empty, it returns the identity element.
    ///
    /// # Type Parameters
    ///
    /// * `I` - The type of the iterator
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator over elements of type `Self`
    ///
    /// # Returns
    ///
    /// The combined result of all elements in the iterator, or the identity element if empty.
    ///
    /// # Examples
    /// ```
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// struct AdditiveInt(i32);
    ///
    /// impl Semigroup<i32> for AdditiveInt {
    ///     fn combine(self, other: Self) -> Self {
    ///         AdditiveInt(self.0 + other.0)
    ///     }
    /// }
    ///
    /// impl Monoid<i32> for AdditiveInt {
    ///     fn empty() -> Self {
    ///         AdditiveInt(0)
    ///     }
    /// }
    ///
    /// let numbers = vec![AdditiveInt(1), AdditiveInt(2), AdditiveInt(3)];
    /// let sum = AdditiveInt::combine_all_monoid(numbers);
    /// assert_eq!(sum.0, 6);
    ///
    /// let empty_vec: Vec<AdditiveInt> = vec![];
    /// let empty_sum = AdditiveInt::combine_all_monoid(empty_vec);
    /// assert_eq!(empty_sum.0, 0);
    /// ```
    fn combine_all_monoid<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Self>,
        Self: Sized,
    {
        iter.into_iter().fold(Self::empty(), |acc, x| acc.combine(x))
    }
}

impl<T> Monoid<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn empty() -> Self {
        Vec::new()
    }
}

impl Monoid<char> for String {
    fn empty() -> Self {
        String::new()
    }
}

impl<T> Monoid<T> for HashSet<T>
where
    T: TypeConstraints + Eq + Hash,
{
    fn empty() -> Self {
        HashSet::new()
    }
}

impl<K, V> Monoid<V> for HashMap<K, V>
where
    K: TypeConstraints + Eq + Hash,
    V: TypeConstraints,
{
    fn empty() -> Self {
        HashMap::new()
    }
}

impl<A, B> Monoid<(A, B)> for (A, B)
where
    A: Monoid<A> + TypeConstraints,
    B: Monoid<B> + TypeConstraints,
{
    fn empty() -> Self {
        (A::empty(), B::empty())
    }
}

impl<A, B, C> Monoid<(A, B, C)> for (A, B, C)
where
    A: Monoid<A> + TypeConstraints,
    B: Monoid<B> + TypeConstraints,
    C: Monoid<C> + TypeConstraints,
{
    fn empty() -> Self {
        (A::empty(), B::empty(), C::empty())
    }
}
