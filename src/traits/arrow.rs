use crate::traits::category::Category;

/// A trait representing arrows in category theory, which generalizes computation from regular functions
/// to more sophisticated notions of computation.
///
/// # Mathematical Definition
///
/// An arrow is a category with additional structure that allows:
/// 1. Lifting pure functions into the arrow type
/// 2. Processing pairs of values
/// 3. Fanout (splitting) computations
///
/// # Laws
///
/// An arrow must satisfy these laws:
///
/// 1. Category Laws:
///    ```text
///    arrow id >>> f = f = f >>> arrow id
///    (f >>> g) >>> h = f >>> (g >>> h)
///    ```
///
/// 2. Arrow Laws:
///    ```text
///    first (f >>> g) = first f >>> first g
///    first (arrow f) = arrow (f × id)
///    first f >>> arr (id × g) = arr (id × g) >>> first f
///    first f >>> arr fst = arr fst >>> f
///    first (first f) >>> arr assoc = arr assoc >>> first f
///    ```
///    where `assoc ((a,b),c) = (a,(b,c))`
///
/// # Type Parameters
///
/// * `B`, `C`, `D`, `E`: Type parameters for the various morphisms
/// * `F`: Function type that can be lifted into an arrow
///
/// # Common Use Cases
///
/// 1. **Pure Function Composition**
///    - Composing functions in a type-safe way
///    - Building complex transformations from simple ones
///
/// 2. **Stateful Computations**
///    - Handling computations with context or state
///    - Managing side effects in a pure way
///
/// 3. **Parallel Processing**
///    - Splitting computations into parallel paths
///    - Combining results from multiple computations
///
/// 4. **Stream Processing**
///    - Processing data streams with rich operations
///    - Composing stream transformations
pub trait Arrow: Category {
    /// Lifts a pure function into an arrow.
    ///
    /// This operation allows regular functions to be used in the arrow framework.
    /// It's the fundamental way to create basic arrows from pure functions.
    ///
    /// # Type Parameters
    ///
    /// * `B`: Input type of the function
    /// * `C`: Output type of the function
    /// * `F`: The function type to be lifted
    ///
    /// # Arguments
    ///
    /// * `f`: The function to lift into an arrow
    ///
    /// # Returns
    ///
    /// A morphism in the arrow category representing the lifted function
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        F: Fn(B) -> C;

    /// Processes the first component of a pair, leaving the second unchanged.
    ///
    /// This is a fundamental operation that allows arrows to operate on part of a value
    /// while preserving the rest. It's essential for composing arrows that work with context.
    ///
    /// # Type Parameters
    ///
    /// * `B`: Input type of the original morphism
    /// * `C`: Output type of the original morphism
    /// * `D`: Type of the unchanged second component
    ///
    /// # Arguments
    ///
    /// * `f`: The morphism to apply to the first component
    ///
    /// # Returns
    ///
    /// A new morphism that applies `f` to the first component of a pair
    fn first<B, C, D>(f: &Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)> {
        let id = Self::arrow(&|d: D| d);
        let pair = Self::arrow(&|(b, d): (B, D)| (b, d));
        let unpair = Self::arrow(&|(c, d): (C, D)| (c, d));
        Self::compose_morphisms(
            &Self::compose_morphisms(&pair, &Self::combine_morphisms(f, &id)),
            &unpair
        )
    }

    /// Processes the second component of a pair, leaving the first unchanged.
    ///
    /// This is the dual of `first`. It can be derived from `first` using appropriate
    /// swapping of components.
    ///
    /// # Type Parameters
    ///
    /// * `B`: Input type of the original morphism
    /// * `C`: Output type of the original morphism
    /// * `D`: Type of the unchanged first component
    ///
    /// # Arguments
    ///
    /// * `f`: The morphism to apply to the second component
    ///
    /// # Returns
    ///
    /// A new morphism that applies `f` to the second component of a pair
    fn second<B, C, D>(f: &Self::Morphism<B, C>) -> Self::Morphism<(D, B), (D, C)> {
        let swap_in = Self::arrow(&|(d, b): (D, B)| (b, d));
        let swap_out = Self::arrow(&|(c, d): (C, D)| (d, c));
        Self::compose_morphisms(
            &Self::compose_morphisms(&swap_in, &Self::first(f)),
            &swap_out
        )
    }

    /// Splits a computation into two parallel paths.
    ///
    /// This operation allows a single input to be processed by two different arrows
    /// simultaneously, collecting their results into a pair.
    ///
    /// # Type Parameters
    ///
    /// * `B`: Input type
    /// * `C`: Output type of the first morphism
    /// * `D`: Output type of the second morphism
    /// * `E`: Additional type parameter for future extensions
    ///
    /// # Arguments
    ///
    /// * `f`: First morphism to apply
    /// * `g`: Second morphism to apply
    ///
    /// # Returns
    ///
    /// A morphism that applies both `f` and `g` to the input
    fn split<B: Clone, C, D, E>(
        f: &Self::Morphism<B, C>,
        g: &Self::Morphism<B, D>
    ) -> Self::Morphism<B, (C, D)> {
        let duplicate = Self::arrow(&|b: B| (b.clone(), b));
        Self::compose_morphisms(
            &duplicate,
            &Self::combine_morphisms(f, g)
        )
    }

    /// Combines two arrows to process pairs in parallel.
    ///
    /// This operation allows two independent arrows to process their respective
    /// inputs simultaneously. It's particularly useful for parallel processing
    /// and maintaining separation of concerns.
    ///
    /// # Type Parameters
    ///
    /// * `B`: Input type for first morphism
    /// * `C`: Output type for first morphism
    /// * `D`: Input type for second morphism
    /// * `E`: Output type for second morphism
    ///
    /// # Arguments
    ///
    /// * `f`: Morphism for processing first component
    /// * `g`: Morphism for processing second component
    ///
    /// # Returns
    ///
    /// A morphism that processes both components of a pair independently
    fn combine_morphisms<B, C, D, E>(
        f: &Self::Morphism<B, C>,
        g: &Self::Morphism<D, E>
    ) -> Self::Morphism<(B, D), (C, E)> {
        Self::compose_morphisms(&Self::first(f), &Self::second(g))
    }
}