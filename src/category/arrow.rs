use crate::category::hkt::ReturnTypeConstraints;
use crate::category::category::Category;
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
pub trait Arrow<A>: Category<A>
where
    A: ReturnTypeConstraints,
{
    /// Lifts a function to an arrow.
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C>;

    /// Takes an arrow on B to an arrow on (B, C).
    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints;

    /// Takes an arrow on B to an arrow on (D, B).
    fn second<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(D, B), (D, C)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        // Default implementation in terms of first
        let swap_in = Self::arrow(FnType::new(|(d, b): (D, B)| (b, d)));
        let swap_out = Self::arrow(FnType::new(|(c, d): (C, D)| (d, c)));
        Self::compose_morphisms(
            Self::compose_morphisms(swap_in, Self::first(f)),
            swap_out
        )
    }

    /// Split on input.
    fn split<B, C, D, E>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<B, D>
    ) -> Self::Morphism<B, (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        E: ReturnTypeConstraints,
    {
        let dup = Self::arrow(FnType::new(|x: B| (x.clone(), x)));
        Self::compose_morphisms(
            dup,
            Self::combine_morphisms(f, g)
        )
    }

    /// Combine on output.
    fn combine_morphisms<B, C, D, E>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<D, E>
    ) -> Self::Morphism<(B, D), (C, E)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        E: ReturnTypeConstraints,
    {
        let first_f = Self::first(f);
        let second_g = Self::second(g);
        Self::compose_morphisms(first_f, second_g)
    }
}