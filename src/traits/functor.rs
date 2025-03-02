use crate::traits::hkt::HKT;

/// A trait for functors, which are type constructors that support mapping over values.
///
/// In category theory, a functor is a mapping between categories that preserves
/// structure. In Rust terms, it's a type constructor that provides a way to apply
/// a function to values while preserving their structure.
///
/// # Functor Laws
///
/// Any implementation of `Functor` should satisfy these laws:
///
/// 1. Identity: `functor.fmap(|x| x) == functor`
///    Mapping the identity function over a functor should return an equivalent functor.
///
/// 2. Composition: `functor.fmap(|x| g(f(x))) == functor.fmap(f).fmap(g)`
///    Mapping a composition of functions should be the same as mapping each function in sequence.
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
///
/// // Implementing Functor for a simple wrapper type
/// struct Box<T>(T);
///
/// impl<T> HKT for Box<T> {
///     type Source = T;
///     type Output<U> = Box<U>;
///     type Source2 = ();
///     type BinaryOutput<U, V> = ();
/// }
///
/// impl<T> Functor for Box<T> {
///     fn fmap<B, F>(&self, f: F) -> Self::Output<B>
///     where
///         F: Fn(&Self::Source) -> B
///     {
///         Box(f(&self.0))
///     }
///
///     // Using the optimized version for static dispatch
///     fn map<B, F: Fn(&T) -> B>(&self, f: F) -> Box<B> {
///         Box(f(&self.0))
///     }
/// }
///
/// // Using the functor
/// let box_of_int = Box(42);
/// let box_of_string = box_of_int.fmap(|x: &i32| x.to_string());
/// assert_eq!(box_of_string.0, "42");
///
/// // Using the optimized version
/// let doubled = box_of_int.map(|x| x * 2);
/// assert_eq!(doubled.0, 84);
///
/// // Using replace to substitute values
/// let replaced = box_of_int.replace(&String::from("hello"));
/// assert_eq!(replaced.0, "hello");
///
/// // Using void to discard values
/// let voided = box_of_int.void();
/// assert_eq!(std::mem::size_of_val(&voided.0), 0); // Unit type
///
/// // Demonstrating functor laws
/// let id_mapped = box_of_int.fmap(|x| *x);
/// assert_eq!(id_mapped.0, box_of_int.0);  // Identity law
///
/// let f = |x: &i32| x + 1;
/// let g = |x: &i32| x * 2;
/// let composed = box_of_int.fmap(|x| g(&f(x)));
/// let sequenced = box_of_int.fmap(f).fmap(g);
/// assert_eq!(composed.0, sequenced.0);  // Composition law
/// ```
pub trait Functor: HKT {
    /// Maps a function over the values in a functor.
    ///
    /// This operation applies the given function to each value inside the
    /// functor, preserving the structure while transforming the contents.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    ///
    /// A new functor containing the transformed values
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B;
    
    /// Maps a function over the values in a functor with static dispatch.
    ///
    /// This is an optimized version of `fmap` that uses static dispatch instead
    /// of dynamic dispatch, potentially improving performance.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    ///
    /// A new functor containing the transformed values
    ///
    /// # Default Implementation
    ///
    /// By default, this calls `fmap`, but implementations can override it
    /// for better performance.
    #[inline]
    fn map<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        self.fmap(&f)
    }
    
    /// Replaces all values in the functor with a constant value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to replace all elements with
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by the given value
    ///
    /// # Default Implementation
    ///
    /// Uses `fmap` to replace all values.
    fn replace<B>(&self, value: &B) -> Self::Output<B>
    where
        B: Clone,
    {
        self.map(|_| value.clone())
    }
    
    /// Void functor - discards the values and replaces them with unit.
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by ()
    ///
    /// # Default Implementation
    ///
    /// Uses `replace` to replace all values with unit.
    #[inline]
    fn void(&self) -> Self::Output<()> {
        self.map(|_| ())
    }
}