/// A trait for higher-kinded types (HKT).
///
/// Higher-kinded types are type constructors that abstract over type constructors.
/// This trait provides a way to work with type constructors in a generic way,
/// enabling functional programming patterns like Functor, Applicative, and Monad.
///
/// # Type Parameters
/// The trait defines two associated types:
/// * `Source`: The input type parameter
/// * `Output<U>`: A type constructor that takes a type parameter `U`
///
/// # Design Notes
///
/// 1. The trait uses associated types instead of generics to work around
///    Rust's lack of direct support for higher-kinded types.
///
/// 2. The `Source` type represents the "current" type parameter, while
///    `Output<U>` represents the ability to swap that type for any other.
///
/// 3. This pattern enables writing generic code that can work with any
///    type constructor, not just specific ones like Option or Vec.
pub trait HKT {
    /// The source type that this higher-kinded type is parameterized over.
    type Source;

    /// The type constructor that can produce new types from the given type U.
    /// This is used to represent the "shape" of the type constructor.
    type Output<U>;
}