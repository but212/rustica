use crate::fntype::FnType;
use crate::fntype::FnTrait;
use crate::category::hkt::ReturnTypeConstraints;

/// A trait for composable functions that can be chained together.
/// 
/// # Type Parameters
/// * `T` - The input type of the first function
/// * `U` - The output type of the first function / input type of the second function
/// * `V` - The output type of the second function
/// 
/// # Laws
/// A Composable instance must satisfy these laws:
/// 1. Identity: For any composable function `f`,
///    `f.compose(identity) = f = identity.compose(f)`
/// 2. Associativity: For any composable functions `f`, `g`, `h`,
///    `f.compose(g).compose(h) = f.compose(g.compose(h))`
/// 3. Type Safety: For any composable functions `f: T -> U`, `g: U -> V`,
///    `f.compose(g)` must type check as `T -> V`
/// 4. Function Preservation: For any composable functions `f`, `g`,
///    `f.compose(g)` must preserve the function-like behavior
/// 5. Order Preservation: For any composable functions `f`, `g`,
///    `f.compose(g)(x) = g(f(x))`
/// 6. Referential Transparency: For any composable functions `f`, `g`,
///    `f.compose(g)` must be referentially transparent if `f` and `g` are
/// 7. Error Propagation: For any composable functions `f`, `g`,
///    `f.compose(g)` must properly propagate errors from both `f` and `g`
/// 8. Pure Composition: For any pure composable functions `f`, `g`,
///    `f.compose(g)` must also be pure
/// 
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::fntype::{FnType, FnTrait};
///
/// #[derive(Default, Eq, Debug, Clone, PartialEq)]
/// struct MyFn;
///
/// impl FnTrait<i32, i64> for MyFn {
///     fn call(&self, x: i32) -> i64 {
///         x as i64 * 2
///     }
/// }
///
/// #[derive(Default, Eq, Debug, Clone, PartialEq)]
/// struct MyOtherFn;
///
/// impl FnTrait<i64, String> for MyOtherFn {
///     fn call(&self, x: i64) -> String {
///         format!("Value: {}", x)
///     }
/// }
///
/// struct MyComposable;
///
/// impl Composable for MyComposable {}
///
/// let f = MyFn;
/// let g = MyOtherFn;
/// let composed_fn = MyComposable::compose(f, g);
/// let result = composed_fn.call(21);
/// assert_eq!(result, "Value: 42");
/// ```
pub trait Composable {
    /// Composes two functions.
    /// 
    /// # Arguments
    /// * `f` - The first function to be composed.
    /// * `g` - The second function to be composed.
    /// 
    /// # Returns
    /// * `FnType<T, V>` - The composed function.
    /// 
    /// # Type Parameters
    /// * `T` - The input type of the first function.
    /// * `U` - The output type of the first function and input type of the second function.
    /// * `V` - The output type of the second function.
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x: T| g.call(f.call(x)))
    }
}
