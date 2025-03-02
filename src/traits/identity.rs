use crate::traits::hkt::HKT;

/// A trait for types that represent identity functions in category theory.
///
/// In category theory, an identity morphism (or identity function) is a morphism that
/// leaves an object unchanged. The Identity trait provides functionality for working
/// with identity functions and accessing values in a type-safe way.
///
/// # Examples
///
/// ```
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
///
/// // A simple wrapper type
/// struct Wrapper<T>(T);
///
/// impl<T> HKT for Wrapper<T> {
///     type Source = T;
///     type Output<U> = Wrapper<U>;
///     type Source2 = ();
///     type BinaryOutput<U, V> = ();
/// }
///
/// impl<T: Clone> Identity for Wrapper<T> {
///     fn value(&self) -> &Self::Source {
///         &self.0
///     }
///     
///     fn try_value(&self) -> Option<&Self::Source> {
///         Some(&self.0)
///     }
///
///     fn pure_identity<A>(value: A) -> Self::Output<A>
///     where
///         Self::Output<A>: Identity,
///         A: Clone,
///     {
///         Wrapper(value)
///     }
/// }
///
/// // Using the Identity trait
/// let wrapped = Wrapper(42);
/// assert_eq!(*wrapped.value(), 42);
///
/// // Using the identity function
/// let x = 5;
/// assert_eq!(<Wrapper<i32> as Identity>::id(x), 5);
/// ```
pub trait Identity: HKT {
    /// Returns a reference to the contained value.
    ///
    /// # Panics
    ///
    /// This method may panic if the container doesn't contain a valid value.
    /// For a non-panicking alternative, use `try_value()`.
    fn value(&self) -> &Self::Source;

    /// Returns a reference to the contained value, if available.
    ///
    /// This method is safer than `value()` as it returns an `Option`
    /// instead of potentially panicking.
    ///
    /// # Default Implementation
    ///
    /// By default, this calls `value()` and wraps the result in `Some`.
    /// Types that might not contain a value should override this method.
    fn try_value(&self) -> Option<&Self::Source> {
        Some(self.value())
    }

    /// The identity function, which returns its input unchanged.
    ///
    /// This function serves as the identity morphism in category theory.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the input value
    ///
    /// # Arguments
    ///
    /// * `a`: The value to return unchanged
    #[inline]
    fn id<A>(a: A) -> A {
        a
    }

    /// Creates an identity instance containing the given value.
    ///
    /// This is a convenience method for creating a new instance of a type
    /// that implements `Identity`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the value to wrap
    ///
    /// # Arguments
    ///
    /// * `value`: The value to wrap
    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
        A: Clone;
}