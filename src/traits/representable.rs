use crate::traits::functor::Functor;

/// A representable functor is a functor that is naturally isomorphic to a function type.
///
/// In category theory, a functor F is representable if there exists an object R such that
/// F(A) ≅ Hom(R, A) for all objects A. This means the functor can be "represented" by
/// functions from some fixed type R.
///
/// # Laws
///
/// A valid representable functor must satisfy the isomorphism laws:
///
/// 1. **tabulate andThen index == identity**:
///    ```text
///    index(tabulate(f), r) = f(r)
///    ```
///
/// 2. **index andThen tabulate == identity**:
///    ```text
///    tabulate(|r| index(fa, r)) = fa
///    ```
///
/// # Examples
///
/// Common representable functors include:
/// - Functions: `(->) R` is represented by `R`
/// - Streams/infinite lists: represented by natural numbers
/// - Trees with a specific shape: represented by paths through the tree
pub trait Representable: Functor {
    /// The representation type that indexes into this functor.
    ///
    /// This type acts as an "index" or "key" that can be used to extract
    /// values from the functor structure.
    type Rep;

    /// Extract a value from the functor at the given index.
    ///
    /// This is the fundamental accessor for representable functors, allowing
    /// you to retrieve the value stored at a specific representation index.
    ///
    /// # Arguments
    ///
    /// * `r` - The representation index to look up
    ///
    /// # Returns
    ///
    /// The value stored at the given index
    fn index<A: Clone>(fa: &Self::Output<A>) -> impl Fn(&Self::Rep) -> A;

    /// Create a representable functor by providing a function from indices to values.
    ///
    /// This is the fundamental constructor for representable functors, allowing
    /// you to build a functor structure by specifying what value should appear
    /// at each possible index.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that maps from representation indices to values
    ///
    /// # Returns
    ///
    /// A new functor containing the values produced by the function
    fn tabulate<F, A>(f: F) -> Self::Output<A>
    where
        F: Fn(&Self::Rep) -> A,
        A: Clone;
}
