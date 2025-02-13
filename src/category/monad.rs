use crate::category::applicative::Applicative;
use crate::category::hkt::TypeConstraints;
use crate::fntype::FnTrait;
use crate::category::category::Category;

/// A trait for monads, which are applicative functors that support sequencing of operations.
/// 
/// # Laws
/// 1. Left Identity: `pure(x).bind(f) = f(x)`
/// 2. Right Identity: `m.bind(pure) = m`
/// 3. Associativity: `m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))`
/// 4. Applicative Consistency: `m.bind(|x| pure(f(x))) = m.fmap(f)`
/// 5. Join Consistency: `m.bind(f) = m.fmap(f).join()`
/// 6. Pure Preservation: `join(pure(pure(x))) = pure(x)`
/// 7. Natural Transformation: `η(m.bind(f)) = η(m).bind(η ∘ f)`
/// 8. Category Consistency: `m.bind(f).bind(g) = m.bind(compose_morphisms(f, g))`
///
/// # Examples
/// ```
/// use rustica::prelude::*;
/// 
/// #[derive(Clone, Debug, PartialEq, Eq, Default)]
/// struct MyMonad<T>(T);
/// 
/// impl<T: TypeConstraints> HKT for MyMonad<T> {
///     type Output<U> = MyMonad<U> where U: TypeConstraints;
/// }
/// 
/// impl<T: TypeConstraints> Functor<T> for MyMonad<T> {
///     fn fmap<U, F>(self, f: F) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         F: FnTrait<T, U>,
///     {
///         MyMonad(f.call(self.0))
///     }
/// }
/// 
/// impl<T: TypeConstraints> Pure<T> for MyMonad<T> {
///     fn pure(x: T) -> Self { MyMonad(x) }
/// }
/// 
/// impl<T: TypeConstraints> Identity for MyMonad<T> {}
/// 
/// impl<T: TypeConstraints> Composable for MyMonad<T> {}
/// 
/// impl<T: TypeConstraints> Category for MyMonad<T> {
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
/// impl<T: TypeConstraints> Applicative<T> for MyMonad<T> {
///     fn apply<U, F>(self, f: Self::Output<F>) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         F: FnTrait<T, U>,
///     {
///         MyMonad(f.0.call(self.0))
///     }
/// 
///     fn lift2<U, C, F>(self, b: Self::Output<U>, f: F) -> Self::Output<C>
///     where
///         U: TypeConstraints,
///         C: TypeConstraints,
///         F: FnTrait<(T, U), C>,
///     {
///         MyMonad(f.call((self.0, b.0)))
///     }
/// 
///     fn lift3<U, C, D, F>(self, b: Self::Output<U>, c: Self::Output<C>, f: F) -> Self::Output<D>
///     where
///         U: TypeConstraints,
///         C: TypeConstraints,
///         D: TypeConstraints,
///         F: FnTrait<(T, U, C), D>,
///     {
///         MyMonad(f.call((self.0, b.0, c.0)))
///     }
/// }
/// 
/// impl<T: TypeConstraints> Monad<T> for MyMonad<T> {
///     fn join<U>(self) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         T: Into<Self::Output<U>>,
///     {
///         self.0.into()
///     }
/// 
///     fn bind<U, F>(self, f: F) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         F: FnTrait<T, Self::Output<U>>,
///     {
///         f.call(self.0)
///     }
/// 
///     fn kleisli_compose<B, C, G, H>(_g: G, _h: H) -> Self::Morphism<T, Self::Output<C>>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         G: FnTrait<T, Self::Output<B>>,
///         H: FnTrait<B, Self::Output<C>>,
///     {
///         unimplemented!()
///     }
/// }
/// 
/// // Test the Monad laws
/// let m = MyMonad(5);
/// let f = FnType::new(|x: i32| MyMonad(x * 2));
/// let g = FnType::new(|x: i32| MyMonad(x + 1));
/// 
/// // Left Identity
/// assert_eq!(MyMonad::pure(5).bind(f.clone()), f.call(5));
/// 
/// // Right Identity
/// assert_eq!(m.clone().bind(FnType::new(MyMonad::pure)), m);
/// 
/// // Associativity
/// assert_eq!(
///     m.clone().bind(f.clone()).bind(g.clone()),
///     m.bind(FnType::new(move |x: i32| f.call(x.clone()).bind(g.clone())))
/// );
/// ```
pub trait Monad<T>: Applicative<T> + Category
where
    T: TypeConstraints,
{
    fn join<U>(self) -> Self::Output<U>
    where
        U: TypeConstraints,
        T: Into<Self::Output<U>>;

    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, Self::Output<U>>;

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> Self::Morphism<T, Self::Output<C>>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        G: FnTrait<T, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    ;
}
