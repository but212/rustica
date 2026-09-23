//! Trait implementations for `Validated`.
//!
//! `Validated<T, E>` represents either a `Valid(T)` or an `Invalid(NonEmptyErrors<E>)`.
//! Like `Result<T, E>`, the success value is the first type parameter and the error
//! collection is the second type parameter.

use crate::datatypes::validated::core::Validated;
use crate::traits::semigroup::Semigroup;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

/// # Semigroup for `Validated`
///
/// Combines two `Validated` values:
/// - If both are `Valid`, their inner values are combined using `T::combine`.
/// - If one is `Invalid` and one is `Valid`, the `Invalid` is returned (errors take precedence).
/// - If both are `Invalid`, their error collections are concatenated.
impl<T: Semigroup, E> Semigroup for Validated<T, E> {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Validated::Valid(a1), Validated::Valid(a2)) => Validated::Valid(a1.combine(a2)),
            (Validated::Valid(_), o @ Validated::Invalid(_)) => o,
            (s @ Validated::Invalid(_), Validated::Valid(_)) => s,
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            },
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<T, E> Arbitrary for Validated<T, E>
where
    T: Arbitrary,
    E: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = T::arbitrary(g);
        let y = E::arbitrary(g);
        if bool::arbitrary(g) {
            Validated::valid(x)
        } else {
            Validated::invalid(y)
        }
    }
}
