use crate::fntype::SendSyncFn;
use crate::fntype::SendSyncFnTrait;
use crate::category::hkt::ReturnTypeConstraints;

/// The `Composable` trait provides a method for function composition.
/// 
/// # Type Parameters
/// * `T` - The input type of the first function
/// * `U` - The output type of the first function and input type of the second function
/// * `V` - The output type of the second function
///
/// # Laws
/// - Associativity: `composable(composable(f, g), h) = composable(f, composable(g, h))`
/// - Identity: `composable(f, |x| x) = f`
/// - Composition: `composable(f, g) = |x| g(f(x))`
/// 
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::fntype::{SendSyncFn, SendSyncFnTrait};
///
/// #[derive(Default, Eq, Debug, Clone, PartialEq)]
/// struct MyFn;
///
/// impl SendSyncFnTrait<i32, i64> for MyFn {
///     fn call(&self, x: i32) -> i64 {
///         x as i64 * 2
///     }
/// }
///
/// #[derive(Default, Eq, Debug, Clone, PartialEq)]
/// struct MyOtherFn;
///
/// impl SendSyncFnTrait<i64, String> for MyOtherFn {
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
    /// * `SendSyncFn<T, V>` - The composed function.
    /// 
    /// # Type Parameters
    /// * `T` - The input type of the first function.
    /// * `U` - The output type of the first function and input type of the second function.
    /// * `V` - The output type of the second function.
    fn compose<T, U, V, F, G>(f: F, g: G) -> SendSyncFn<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
        G: SendSyncFnTrait<U, V>,
    {
        SendSyncFn::new(move |x: T| g.call(f.call(x)))
    }
}
