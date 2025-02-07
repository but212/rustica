use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::SendSyncFnTrait;
use crate::category::monad::Monad;

/// A trait for types that support flattening of nested structures.
/// 
/// # Type Parameters
/// * `T` - The type of the value within the structure.
/// 
/// # Laws
/// A FlatMap instance must satisfy these laws:
/// 1. Associativity: For any value `m` and functions `f`, `g`,
///    `m.flat_map(f).flat_map(g) = m.flat_map(|x| f(x).flat_map(g))`
/// 2. Consistency with Map: For any value `m` and function `f`,
///    `m.flat_map(|x| pure(f(x))) = m.map(f)`
/// 3. Flattening Identity: For any value `m`,
///    `flatten(pure(m)) = m`
/// 4. Map-Flatten Consistency: For any value `m` and function `f`,
///    `m.flat_map(f) = flatten(map(f)(m))`
pub trait FlatMap<T>: Monad<T> + Sized
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the value and flattens the result.
    ///
    /// # Arguments
    /// - `self`: The monad instance.
    /// - `f`: A function that takes a value of type `T` and returns a monad containing a value of type `U`.
    ///
    /// # Returns
    /// A new monad containing the result of applying the function `f` to the value.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `T` and returns a monad containing a value of type `U`.
    fn flat_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, Self::Output<U>>,
    {
        self.bind(f)
    }
}
