use crate::traits::hkt::TypeConstraints;
use crate::traits::category::Category;
use crate::fntype::FnTrait;
use crate::fntype::FnType;

/// Arrow type class.
///
/// # Type Parameters
/// * `A` - The base type for this arrow
/// * `Morphism<B, C>` - The type of morphisms from B to C in this category.
///
/// # Laws
/// An arrow must satisfy these laws:
/// 1. arrow id >>> f = f = f >>> arrow id
/// 2. (f >>> g) >>> h = f >>> (g >>> h)
/// 3. first (f >>> g) = first f >>> first g
/// 4. first (arrow f) = arrow (f × id)
/// 5. first f >>> arrow (id × g) = arrow (id × g) >>> first f
/// 6. first f >>> arrow fst = arrow fst >>> f
/// 7. first (first f) >>> arrow assoc = arrow assoc >>> first f
///
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// struct MyArrow;
///
/// impl HKT for MyArrow {
///     type Output<A> = A where A: TypeConstraints;
/// }
///
/// impl Identity for MyArrow {
///     fn identity<A: TypeConstraints>(x: A) -> A {
///         x
///     }
/// }
/// 
/// impl Composable for MyArrow {
///     fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
///     where
///         T: TypeConstraints,
///         U: TypeConstraints,
///         V: TypeConstraints,
///         F: FnTrait<T, U>,
///         G: FnTrait<U, V>,
///     {
///         FnType::new(move |x| g.call(f.call(x)))
///     }
/// }
/// 
/// impl Category for MyArrow {
///     type Morphism<A, B> = FnType<A, B> where A: TypeConstraints, B: TypeConstraints;
///
///     fn identity_morphism<A: TypeConstraints>() -> Self::Morphism<A, A> {
///         FnType::new(|x| x)
///     }
///
///     fn compose_morphisms<A, B, C>(f: Self::Morphism<A, B>, g: Self::Morphism<B, C>) -> Self::Morphism<A, C>
///     where
///         A: TypeConstraints,
///         B: TypeConstraints,
///         C: TypeConstraints,
///     {
///         FnType::new(move |x| g.call(f.call(x)))
///     }
/// }
///
/// impl Arrow for MyArrow {
///     fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         F: FnTrait<B, C>,
///     {
///         FnType::new(move |x| f.call(x))
///     }
///
///     fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         D: TypeConstraints,
///     {
///         FnType::new(move |(b, d)| (f.call(b), d))
///     }
/// }
///
/// let add_one = MyArrow::arrow(FnType::new(|x: i32| x + 1));
/// let multiply_by_two = MyArrow::arrow(FnType::new(|x: i32| x * 2));
/// let combined = MyArrow::compose_morphisms(add_one, multiply_by_two);
/// assert_eq!(combined.call(3), 8);
/// ```
pub trait Arrow: Category {
    /// Creates an arrow from a function.
    ///
    /// This method lifts a regular function into the arrow category.
    ///
    /// # Type Parameters
    /// * `B`: The input type of the function
    /// * `C`: The output type of the function
    /// * `F`: The function type
    ///
    /// # Arguments
    /// * `f`: The function to be lifted into an arrow
    ///
    /// # Returns
    /// A morphism in the arrow category representing the given function
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<B, C>
    {
        FnTrait::new(move |x| f.call(x))
    }

    /// Applies a morphism to the first component of a pair.
    ///
    /// This method takes a morphism `f: B -> C` and returns a new morphism that
    /// applies `f` to the first component of a pair `(B, D)`, leaving the second
    /// component unchanged.
    ///
    /// # Type Parameters
    /// * `B`: The input type of the original morphism
    /// * `C`: The output type of the original morphism
    /// * `D`: The type of the second component in the pair
    ///
    /// # Arguments
    /// * `f`: The morphism to be applied to the first component
    ///
    /// # Returns
    /// A new morphism that operates on pairs, applying `f` to the first component
    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnTrait::new(move |x: (B, D)| (f.call(x.0), x.1))
    }

    /// Applies a morphism to the second component of a pair.
    ///
    /// This method takes a morphism `f: B -> C` and returns a new morphism that
    /// applies `f` to the second component of a pair `(D, B)`, leaving the first
    /// component unchanged.
    ///
    /// # Type Parameters
    /// * `B`: The input type of the original morphism
    /// * `C`: The output type of the original morphism
    /// * `D`: The type of the first component in the pair
    ///
    /// # Arguments
    /// * `f`: The morphism to be applied to the second component
    ///
    /// # Returns
    /// A new morphism that operates on pairs, applying `f` to the second component
    fn second<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(D, B), (D, C)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        let swap_in = Self::arrow(FnType::new(|(d, b): (D, B)| (b, d)));
        let swap_out = Self::arrow(FnType::new(|(c, d): (C, D)| (d, c)));
        Self::compose_morphisms(
            Self::compose_morphisms(swap_in, Self::first(f)),
            swap_out
        )
    }

    /// Splits a single input into two outputs using two different morphisms.
    ///
    /// This method takes two morphisms, `f: B -> C` and `g: B -> D`, and combines them
    /// to create a new morphism that applies both `f` and `g` to the same input,
    /// producing a pair of their results.
    ///
    /// # Type Parameters
    /// * `B`: The input type for both morphisms
    /// * `C`: The output type of the first morphism
    /// * `D`: The output type of the second morphism
    /// * `E`: Unused type parameter (consider removing if not needed)
    ///
    /// # Arguments
    /// * `f`: The first morphism to apply
    /// * `g`: The second morphism to apply
    ///
    /// # Returns
    /// A new morphism that applies both `f` and `g` to the input and returns their results as a pair
    fn split<B, C, D, E>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<B, D>
    ) -> Self::Morphism<B, (C, D)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        E: TypeConstraints,
    {
        let dup = Self::arrow(FnType::new(|x: B| (x.clone(), x)));
        Self::compose_morphisms(
            dup,
            Self::combine_morphisms(f, g)
        )
    }

    /// Combines two morphisms to operate on pairs.
    ///
    /// This method takes two morphisms, `f: B -> C` and `g: D -> E`, and combines them
    /// to create a new morphism that applies `f` to the first component of a pair and
    /// `g` to the second component.
    ///
    /// # Type Parameters
    /// * `B`: The input type of the first morphism
    /// * `C`: The output type of the first morphism
    /// * `D`: The input type of the second morphism
    /// * `E`: The output type of the second morphism
    ///
    /// # Arguments
    /// * `f`: The morphism to apply to the first component
    /// * `g`: The morphism to apply to the second component
    ///
    /// # Returns
    /// A new morphism that applies `f` and `g` to the respective components of a pair
    fn combine_morphisms<B, C, D, E>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<D, E>
    ) -> Self::Morphism<(B, D), (C, E)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        E: TypeConstraints,
    {
        let first_f = Self::first(f);
        let second_g = Self::second(g);
        Self::compose_morphisms(first_f, second_g)
    }
}