use crate::fntype::FnType;
use crate::fntype::FnTrait;
use crate::traits::hkt::TypeConstraints;

/// A trait for composable functions that can be chained together.
///
/// # Laws
/// 1. Identity: `f.compose(identity) = f = identity.compose(f)`
/// 2. Associativity: `f.compose(g).compose(h) = f.compose(g.compose(h))`
/// 3. Type Safety: `f: T -> U`, `g: U -> V`, then `f.compose(g): T -> V`
/// 4. Function Preservation: `f.compose(g)` preserves function-like behavior
/// 5. Order Preservation: `f.compose(g)(x) = g(f(x))`
/// 6. Referential Transparency: `f.compose(g)` is referentially transparent if `f` and `g` are
/// 7. Error Propagation: `f.compose(g)` propagates errors from both `f` and `g`
/// 8. Pure Composition: If `f` and `g` are pure, `f.compose(g)` is pure
///
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// struct MyComposable;
///
/// impl Composable for MyComposable {}
///
/// let f = FnType::new(|x: i32| x + 1);
/// let g = FnType::new(|x: i32| x * 2);
/// let h = MyComposable::compose(f, g);
///
/// assert_eq!(h.call(3), 8);
/// ```
pub trait Composable {
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: TypeConstraints,
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}
