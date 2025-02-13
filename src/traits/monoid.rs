use crate::traits::hkt::TypeConstraints;
use crate::traits::semigroup::Semigroup;

/// A trait for monoids, which are semigroups with an identity element.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the monoid
/// 
/// # Laws
/// A Monoid instance must satisfy these laws:
/// 1. Identity: For any value `x`,
///    `x.combine(empty()) = x = empty().combine(x)`
/// 2. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = (x.combine(y)).combine(z)`
/// 3. Empty Uniqueness: For any monoid `M`,
///    There exists a unique empty element `e` such that `e.combine(x) = x = x.combine(e)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.combine(y)) = η(x).combine(η(y))`
/// 5. Empty Preservation: For any natural transformation `η`,
///    `η(empty()) = empty()`
/// 6. Distributivity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = x.combine(y).combine(x.combine(z))`
/// 7. Commutativity (if applicable): For any values `x`, `y`,
///    `x.combine(y) = y.combine(x)`
/// 8. Cancellation (if applicable): For any values `x`, `y`, `z`,
///    If `x.combine(y) = x.combine(z)` then `y = z`
pub trait Monoid: Semigroup {
    /// The identity element of the monoid.
    ///
    /// # Returns
    /// The identity element of the monoid.
    fn empty() -> Self;
}

/// A monoid for vectors.
impl<T> Monoid for Vec<T>
where
    T: TypeConstraints,
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
