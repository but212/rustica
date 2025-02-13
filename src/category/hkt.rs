use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::Hash;

/// Common type constraints for return types in functional programming constructs.
///
/// This trait defines a set of common constraints that return types must satisfy
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
pub trait ReturnTypeConstraints: Clone + Debug + PartialEq + Eq + Default + Send + Sync + 'static {}

/// Blanket implementation for types satisfying the `ReturnTypeConstraints` requirements.
///
/// This implementation automatically implements `ReturnTypeConstraints` for any type
/// that satisfies all the required trait bounds.
impl<T> ReturnTypeConstraints for T where T: Clone + Debug + PartialEq + Eq + Default + Send + Sync + 'static {}


/// A trait for higher-kinded types (HKT).
///
/// This trait enables type-level programming by allowing types to be parameterized
/// over other type constructors. It serves as a foundation for implementing
/// functional programming patterns like Functor, Applicative, and Monad.
///
/// # Associated Types
///
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
pub trait HKT {
    type Output<U>: ReturnTypeConstraints
    where
        U: ReturnTypeConstraints;
}



/// Implements the HKT trait for Vec<T>.
///
/// This implementation allows Vec to be parameterized over other type constructors,
/// enabling functional programming patterns like Functor, Applicative, and Monad.
///
/// # Associated Types
///
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
impl<T> HKT for Vec<T>
where
    T: ReturnTypeConstraints,
{
    type Output<U> = Vec<U> where U: ReturnTypeConstraints;
}

/// Implements the HKT trait for Box<T>.
///
/// This implementation allows Box to be parameterized over other type constructors,
/// enabling functional programming patterns like Functor, Applicative, and Monad.
///
/// # Associated Types
///
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
impl<T> HKT for Box<T>
where
    T: ReturnTypeConstraints,
{
    type Output<U> = Box<U> where U: ReturnTypeConstraints;
}

/// Implements the HKT trait for HashMap<K, V>.
///
/// This implementation allows HashMap to be parameterized over other type constructors,
/// enabling functional programming patterns like Functor, Applicative, and Monad.
///
/// # Associated Types
///
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
///
/// # Constraints
///
/// * `K` - Must implement `Hash`, `Eq`, `Send`, `Sync`, `Clone`, `Debug`, and `'static`.
/// * `V` - Must implement `ReturnTypeConstraints`.
impl<K, V> HKT for HashMap<K, V>
where
    K: Hash + Eq + Send + Sync + Clone + Debug + 'static,
    V: ReturnTypeConstraints,
{
    type Output<U> = HashMap<K, U> where U: ReturnTypeConstraints;
}
