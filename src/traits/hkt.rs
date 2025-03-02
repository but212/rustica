/// A trait for higher-kinded types (HKT).
///
/// Higher-kinded types are type constructors that abstract over other type constructors.
/// This trait provides a way to work with type constructors in a generic way in Rust.
///
/// # Examples
///
/// ```
/// use rustica::traits::hkt::HKT;
///
/// // A simple container that implements HKT
/// struct Container<T>(T);
///
/// impl<T> HKT for Container<T> {
///     type Source = T;
///     type Output<U> = Container<U>;
///     type Source2 = ();
///     type BinaryOutput<U, V> = ();
/// }
///
/// // Creating a Container with different types
/// let int_container = Container(42);
/// let str_container = Container("hello");
/// ```
pub trait HKT {
    /// The source type that this higher-kinded type is parameterized over.
    ///
    /// This represents the current type parameter of the type constructor.
    type Source;

    /// The type constructor that can produce new types from the given type `U`.
    ///
    /// This represents the ability to apply the type constructor to a new type parameter.
    type Output<U>;

    /// Optional second source type for types with multiple parameters.
    /// Default implementation returns `()` for single-parameter types.
    type Source2;

    /// Optional output type for binary type constructors.
    /// Types with two parameters can override this.
    type BinaryOutput<U, V>;
}