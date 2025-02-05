use std::fmt::Debug;
use std::collections::HashMap;
use std::hash::Hash;

/// Common type constraints for return types in functional programming constructs.
///
/// This trait defines a set of common constraints that return types must satisfy
/// in various functional programming constructs. It ensures that types implementing
/// this trait are cloneable, debuggable, comparable, sendable across threads, 
/// synchronizable, default-constructible, and have a static lifetime.
///
/// # Constraints
///
/// * `Clone` - The type must implement the `Clone` trait.
/// * `Debug` - The type must implement the `Debug` trait.
/// * `Eq` - The type must implement the `Eq` trait.
/// * `Send` - The type must implement the `Send` trait, allowing it to be transferred across thread boundaries.
/// * `Sync` - The type must implement the `Sync` trait, allowing it to be referenced from multiple threads.
/// * `Default` - The type must implement the `Default` trait, providing a default value.
/// * `'static` - The type must have a static lifetime, meaning it does not contain any non-static references.
pub trait ReturnTypeConstraints: Clone + Debug + Eq + Send + Sync + Default + 'static {}

/// Implements the `ReturnTypeConstraints` trait for any type that satisfies the required constraints.
///
/// This implementation ensures that any type `T` that implements `Clone`, `Debug`, `Eq`,
/// `Send`, `Sync`, `Default`, and has a static lifetime, will automatically implement the
/// `ReturnTypeConstraints` trait.
impl<T: Clone + Debug + Eq + Send + Sync + Default + 'static> ReturnTypeConstraints for T {}


/// A trait for higher-kinded types (HKT).
///
/// This trait enables type-level programming by allowing types to be parameterized
/// over other type constructors. It serves as a foundation for implementing
/// functional programming patterns like Functor, Applicative, and Monad.
///
/// # Associated Types
///
/// * `Output<U>` - The resulting type when applying the type constructor to a new type `U`.
///
/// # Example
///
/// ```rust
/// // Define a type that implements the HKT trait
/// use rustica::category::hkt::{HKT, ReturnTypeConstraints};
/// 
/// #[derive(Default, PartialEq, Debug, Clone)]
/// struct MyType<A>
/// where
///     A: ReturnTypeConstraints,
/// {
///     value: A,
/// }
/// 
/// impl<U> HKT for MyType<U> 
/// where
///     U: ReturnTypeConstraints,
/// {
///     type Output<T> = MyType<T> where T: ReturnTypeConstraints;
/// }
/// 
/// // Usage example
/// let instance: MyType<i32> = MyType { value: 42 };
/// // Note: The map function is not part of the HKT trait.
/// ```
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
