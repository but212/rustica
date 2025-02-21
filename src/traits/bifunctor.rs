use crate::fntype::FnTrait;
use crate::traits::hkt::{HKT, TypeConstraints};

/// A trait for bifunctors, which are functors that can map over two type parameters.
/// 
/// Bifunctors generalize the concept of functors to structures with two type parameters.
/// They provide operations to map over either or both of these parameters independently.
/// 
/// # Type Parameters
/// * `A`: The first type parameter of the bifunctor
/// * `B`: The second type parameter of the bifunctor
/// 
/// # Laws
/// 
/// A Bifunctor instance must satisfy these laws:
/// 
/// 1. Identity: For any bifunctor `b`,
///    `bimap(id, id)(b) = b`
/// 2. Composition: For any functions `f`, `g`, `h`, `i` and bifunctor `b`,
///    `bimap(f.compose(g), h.compose(i))(b) = bimap(f, h)(bimap(g, i)(b))`
/// 3. First Map Identity: For any bifunctor `b`,
///    `first(id)(b) = b`
/// 4. Second Map Identity: For any bifunctor `b`,
///    `second(id)(b) = b`
/// 5. First-Second Consistency: For any functions `f`, `g` and bifunctor `b`,
///    `bimap(f, g)(b) = first(f)(second(g)(b))`
pub trait Bifunctor<A, B>: HKT
where
    A: TypeConstraints,
    B: TypeConstraints,
{
    /// The type constructor for the bifunctor, representing the result of mapping.
    type Output<C, D>: HKT where C: TypeConstraints, D: TypeConstraints;

    /// Maps a function over the first type parameter of the bifunctor.
    /// 
    /// # Type Parameters
    /// * `C`: The new type for the first parameter after mapping
    /// * `F`: The function type, must implement `FnTrait<A, C>`
    /// 
    /// # Parameters
    /// * `self`: The bifunctor instance
    /// * `f`: The function to apply to the first type parameter
    /// 
    /// # Returns
    /// A new bifunctor with the first type parameter mapped
    fn first<C, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<C, B>
    where
        C: TypeConstraints,
        F: FnTrait<A, C>;

    /// Maps a function over the second type parameter of the bifunctor.
    /// 
    /// # Type Parameters
    /// * `D`: The new type for the second parameter after mapping
    /// * `F`: The function type, must implement `FnTrait<B, D>`
    /// 
    /// # Parameters
    /// * `self`: The bifunctor instance
    /// * `f`: The function to apply to the second type parameter
    /// 
    /// # Returns
    /// A new bifunctor with the second type parameter mapped
    fn second<D, F>(self, f: F) -> <Self as Bifunctor<A, B>>::Output<A, D>
    where
        D: TypeConstraints,
        F: FnTrait<B, D>;

    /// Maps functions over both type parameters of the bifunctor simultaneously.
    /// 
    /// # Type Parameters
    /// * `C`: The new type for the first parameter after mapping
    /// * `D`: The new type for the second parameter after mapping
    /// * `F`: The function type for the first parameter, must implement `FnTrait<A, C>`
    /// * `G`: The function type for the second parameter, must implement `FnTrait<B, D>`
    /// 
    /// # Parameters
    /// * `self`: The bifunctor instance
    /// * `f`: The function to apply to the first type parameter
    /// * `g`: The function to apply to the second type parameter
    /// 
    /// # Returns
    /// A new bifunctor with both type parameters mapped
    fn bimap<C, D, F, G>(self, f: F, g: G) -> <Self as Bifunctor<A, B>>::Output<C, D>
    where
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<A, C>,
        G: FnTrait<B, D>;
}