use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::Hash;

/// Common type constraints for types in functional programming constructs.
///
/// This trait defines a set of common constraints that types must satisfy
/// in various functional programming constructs. It ensures that types implementing
/// this trait are cloneable, comparable, debuggable, defaultable, sendable across threads,
/// synchronizable, and have a static lifetime.
///
/// # Constraints
///
/// * `Clone`: The type can be duplicated.
/// * `Debug`: The type can be formatted for debugging purposes.
/// * `PartialEq`: The type supports partial equality comparisons.
/// * `Eq`: The type supports full equality comparisons.
/// * `Default`: The type has a default value.
/// * `Send`: The type can be safely transferred across thread boundaries.
/// * `Sync`: The type can be safely shared between threads.
/// * `'static`: The type has a static lifetime (no non-static references).
pub trait TypeConstraints: Clone + Debug + PartialEq + Eq + Default + Send + Sync + 'static {}

/// Blanket implementation for types satisfying the `TypeConstraints` requirements.
///
/// This implementation automatically implements `TypeConstraints` for any type
/// that satisfies all the required trait bounds.
impl<T> TypeConstraints for T where T: Clone + Debug + PartialEq + Eq + Default + Send + Sync + 'static {}

/// A trait for higher-kinded types (HKT).
///
/// This trait enables type-level programming by allowing types to be parameterized
/// over other type constructors. It serves as a foundation for implementing
/// functional programming patterns like Functor, Applicative, and Monad.
///
/// # Type Parameters
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
///
/// # Examples
/// ```rust
/// use rustica::traits::hkt::{HKT, TypeConstraints};
///
/// #[derive(Clone, Debug, PartialEq, Eq, Default)]
/// struct Container<T>(T);
///
/// impl<T: TypeConstraints> HKT for Container<T> {
///     type Output<U> = Container<U> where U: TypeConstraints;
/// }
/// ```
pub trait HKT: TypeConstraints {
    type Output<U>: TypeConstraints where U: TypeConstraints;
}

// Standard implementations
impl<T: TypeConstraints> HKT for Vec<T> {
    type Output<U> = Vec<U> where U: TypeConstraints;
}

impl<T: TypeConstraints> HKT for Option<T> {
    type Output<U> = Option<U> where U: TypeConstraints;
}

impl<T: TypeConstraints> HKT for Box<T> {
    type Output<U> = Box<U> where U: TypeConstraints;
}

impl<K, V> HKT for HashMap<K, V>
where
    K: Hash + Eq + Send + Sync + Clone + Debug + 'static,
    V: TypeConstraints,
{
    type Output<U> = HashMap<K, U> where U: TypeConstraints;
}
