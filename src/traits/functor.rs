use crate::traits::hkt::HKT;

/// A trait for functors, which are type constructors that support mapping over values.
///
/// In category theory, a functor is a mapping between categories that preserves
/// structure. In Rust terms, it's a type constructor that provides a way to apply
/// a function to values while preserving their structure.
///
/// # Type Parameters
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type of values being mapped over
/// * `Output<T>` represents the result type after mapping
///
/// # Laws
/// For a valid Functor implementation:
///
/// 1. Identity:
///    x.fmap(|a| a) == x
///
/// 2. Composition:
///    x.fmap(|a| f(g(a))) == x.fmap(g).fmap(f)
///
/// # Examples
///
/// Basic implementation for Option:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
/// use rustica::traits::functor::Functor;
/// 
/// struct MyOption<T>(Option<T>);
/// 
/// impl<T> HKT for MyOption<T> {
///     type Source = T;
///     type Output<U> = MyOption<U>;
/// }
/// 
/// impl<T> Identity for MyOption<T> {
///     fn value(&self) -> &Self::Source {
///         self.0.as_ref().unwrap()
///     }
/// }
///
/// impl<T> Functor for MyOption<T> {
///     fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
///         MyOption(self.0.as_ref().map(f))
///     }
/// }
///
/// // Usage
/// let opt = MyOption(Some(42));
/// let result = opt.fmap(&|x| x * 2);
/// assert_eq!(result.0, Some(84));
/// ```
///
/// Implementation for a custom vector wrapper:
/// ```rust 
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
/// use rustica::traits::functor::Functor;
/// 
/// struct MyVec<T>(Vec<T>);
/// 
/// impl<T> HKT for MyVec<T> {
///     type Source = T;
///     type Output<U> = MyVec<U>;
/// }
/// 
/// impl<T> Identity for MyVec<T> {
///     fn value(&self) -> &Self::Source {
///         &self.0[0]
///     }
/// }
///
/// impl<T> Functor for MyVec<T> {
///     fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
///         MyVec(self.0.iter().map(f).collect())
///     }
/// }
///
/// // Usage
/// let numbers = MyVec(vec![1, 2, 3]);
/// let doubled = numbers.fmap(&|x| x * 2);
/// assert_eq!(doubled.0, vec![2, 4, 6]);
/// ```
///
/// # Design Notes
///
/// 1. Functors should preserve the structure of the container while
///    transforming its contents.
///
/// 2. The mapping function should be pure (no side effects) to maintain
///    functor laws.
///
/// 3. Functor implementations should be efficient, considering whether
///    to transform eagerly or lazily.
pub trait Functor: HKT {
    /// Maps a function over the values in a functor.
    ///
    /// This operation applies the given function to each value inside the
    /// functor, preserving the structure while transforming the contents.
    ///
    /// # Type Parameters
    /// * `B`: The type that the function produces
    ///
    /// # Arguments
    /// * `f`: A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    /// A new functor containing the transformed values
    fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B>;
}