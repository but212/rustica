/// An enhanced trait for higher-kinded types (HKT) with improved type parameter handling.
///
/// This trait extends the original HKT concept with better support for generic constraints
/// and type parameter relations. It provides a way to work with type constructors in a
/// more flexible and typesafe manner.
///
/// # Type Parameters
///
/// * `F<_>`: A higher-kinded type constructor that can be applied to different types
/// * `A`: The current type parameter applied to the type constructor
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply};
///
/// // Define a simple container with EnhancedHKT
/// struct Container<T>(T);
///
/// // Implementation for the type constructor
/// impl<T> EnhancedHKT for Container<T> {
///     type Parameter = T;
/// }
///
/// // Implementation for applying the type constructor to a new type
/// impl<T, U> HKTApply<U> for Container<T> {
///     type Applied = Container<U>;
/// }
///
/// // Creating containers with different types
/// let int_container = Container(42);
/// let str_container = Container("hello");
/// ```
pub trait EnhancedHKT {
    /// The current type parameter of this higher-kinded type.
    type Parameter;
}

/// A trait for applying a higher-kinded type to a new type parameter.
///
/// This trait allows type constructors to be applied to different type parameters,
/// providing the foundation for higher-kinded polymorphism.
///
/// # Type Parameters
///
/// * `U`: The new type parameter to apply to the type constructor
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply};
///
/// // A simple generic type
/// struct Box<T>(T);
///
/// impl<T> EnhancedHKT for Box<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for Box<T> {
///     type Applied = Box<U>;
/// }
///
/// // Map from Box<i32> to Box<String>
/// fn map_box<T, U, F>(box_t: Box<T>, f: F) -> Box<U>
/// where
///     F: FnOnce(T) -> U,
///     Box<T>: HKTApply<U>,
/// {
///     let Box(value) = box_t;
///     Box(f(value))
/// }
/// ```
pub trait HKTApply<U>: EnhancedHKT {
    /// The result of applying this type constructor to the new type parameter.
    type Applied;
}

/// A trait for constraining higher-kinded types.
///
/// This trait allows for expressing constraints on the type parameters of
/// higher-kinded types, enabling more type-safe generic code.
///
/// # Type Parameters
///
/// * `C`: The constraint to apply to the type parameter
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTConstraint};
/// use std::fmt::Display;
///
/// // A container with a constraint
/// struct DisplayBox<T: Display>(T);
///
/// impl<T: Display> EnhancedHKT for DisplayBox<T> {
///     type Parameter = T;
/// }
///
/// impl<T: Display, U: Display> HKTApply<U> for DisplayBox<T> {
///     type Applied = DisplayBox<U>;
/// }
///
/// // Expressing that the type parameter must implement Display
/// impl<T: Display> HKTConstraint<dyn Display> for DisplayBox<T> {}
///
/// // Function that requires a Display constraint
/// fn print_box<F, T>(box_t: F)
/// where
///     F: EnhancedHKT<Parameter = T>,
///     F: HKTConstraint<dyn Display>,
///     T: Display,
/// {
///     // Now we know T implements Display
///     println!("Box contains: {}", box_t.get_value());
/// }
/// ```
pub trait HKTConstraint<C>: EnhancedHKT {}

/// A trait for composing higher-kinded types.
///
/// This trait allows for nested application of higher-kinded types,
/// enabling composition of type constructors.
///
/// # Type Parameters
///
/// * `G`: Another higher-kinded type
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTCompose};
///
/// // Two simple containers
/// struct Box<T>(T);
/// struct List<T>(Vec<T>);
///
/// impl<T> EnhancedHKT for Box<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for Box<T> {
///     type Applied = Box<U>;
/// }
///
/// impl<T> EnhancedHKT for List<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for List<T> {
///     type Applied = List<U>;
/// }
///
/// // Compose Box and List to get Box<List<T>>
/// impl<T, G> HKTCompose<G> for Box<T>
/// where
///     G: EnhancedHKT,
/// {
///     type Composed = Box<G>;
/// }
///
/// // Now we can have Box<List<int>> etc.
/// ```
pub trait HKTCompose<G>: EnhancedHKT
where
    G: EnhancedHKT,
{
    /// The result of composing this type constructor with another.
    type Composed;
}

/// A trait for lifting a value into a higher-kinded context.
///
/// This trait is similar to the `Pure` trait in the original implementation but
/// works with the enhanced HKT system.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTLift};
///
/// // An option-like type
/// enum Maybe<T> {
///     Just(T),
///     Nothing,
/// }
///
/// impl<T> EnhancedHKT for Maybe<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for Maybe<T> {
///     type Applied = Maybe<U>;
/// }
///
/// impl<T> HKTLift for Maybe<T> {
///     fn lift<U>(value: U) -> <Self as HKTApply<U>>::Applied {
///         Maybe::Just(value)
///     }
/// }
///
/// // Using lift
/// let maybe_int = Maybe::<()>::lift(42);
/// match maybe_int {
///     Maybe::Just(x) => assert_eq!(x, 42),
///     Maybe::Nothing => panic!("Expected Just"),
/// }
/// ```
pub trait HKTLift: EnhancedHKT {
    /// Lifts a value into this higher-kinded context.
    fn lift<U>(value: U) -> <Self as HKTApply<U>>::Applied
    where
        Self: HKTApply<U>;
}

/// A trait for mapping over the value in a higher-kinded type.
///
/// This trait is similar to the `Functor` trait in the original implementation but
/// works with the enhanced HKT system.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTMap};
///
/// // A simple container
/// struct Box<T>(T);
///
/// impl<T> EnhancedHKT for Box<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for Box<T> {
///     type Applied = Box<U>;
/// }
///
/// impl<T> HKTMap for Box<T> {
///     fn map<U, F>(self, f: F) -> <Self as HKTApply<U>>::Applied
///     where
///         F: FnOnce(Self::Parameter) -> U,
///         Self: HKTApply<U>,
///     {
///         Box(f(self.0))
///     }
/// }
///
/// // Using map
/// let box_int = Box(42);
/// let box_string = box_int.map(|x| x.to_string());
/// assert_eq!(box_string.0, "42");
/// ```
pub trait HKTMap: EnhancedHKT {
    /// Maps a function over the value in this higher-kinded type.
    fn map<U, F>(self, f: F) -> <Self as HKTApply<U>>::Applied
    where
        F: FnOnce(Self::Parameter) -> U,
        Self: HKTApply<U>;
}

/// A trait for binding a function that returns a higher-kinded type.
///
/// This trait is similar to the `Monad` trait in the original implementation but
/// works with the enhanced HKT system.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTBind};
///
/// // An option-like type
/// enum Maybe<T> {
///     Just(T),
///     Nothing,
/// }
///
/// impl<T> EnhancedHKT for Maybe<T> {
///     type Parameter = T;
/// }
///
/// impl<T, U> HKTApply<U> for Maybe<T> {
///     type Applied = Maybe<U>;
/// }
///
/// impl<T> HKTBind for Maybe<T> {
///     fn bind<U, F>(self, f: F) -> <Self as HKTApply<U>>::Applied
///     where
///         F: FnOnce(Self::Parameter) -> <Self as HKTApply<U>>::Applied,
///         Self: HKTApply<U>,
///     {
///         match self {
///             Maybe::Just(x) => f(x),
///             Maybe::Nothing => Maybe::Nothing,
///         }
///     }
/// }
///
/// // Using bind
/// let maybe_int = Maybe::Just(42);
/// let result = maybe_int.bind(|x| {
///     if x > 0 {
///         Maybe::Just(x.to_string())
///     } else {
///         Maybe::Nothing
///     }
/// });
/// match result {
///     Maybe::Just(s) => assert_eq!(s, "42"),
///     Maybe::Nothing => panic!("Expected Just"),
/// }
/// ```
pub trait HKTBind: EnhancedHKT {
    /// Binds a function that returns a higher-kinded type.
    fn bind<U, F>(self, f: F) -> <Self as HKTApply<U>>::Applied
    where
        F: FnOnce(Self::Parameter) -> <Self as HKTApply<U>>::Applied,
        Self: HKTApply<U>;
}
