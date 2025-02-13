use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use crate::traits::hkt::{HKT, TypeConstraints};
use crate::fntype::FnTrait;

/// A trait for functors, which are type constructors that can fmap a function over their contents.
/// 
/// # Type Parameters
/// * `T` - The type of value contained in the functor
/// 
/// # Laws
/// A Functor instance must satisfy these laws:
/// 1. Identity: For any functor `f`, `f.fmap(|x| x) = f`
/// 2. Composition: For any functor `f` and functions `g`, `h`, `f.fmap(|x| h(g(x))) = f.fmap(g).fmap(h)`
/// 3. Naturality: For any natural transformation `η: F ~> G`, `η(f.fmap(g)) = η(f).fmap(g)`
/// 4. Container Preservation: For any functor `f` and function `g`, `f.fmap(g)` must preserve the structure of `f`
/// 5. Type Preservation: For any functor `f` and function `g`, `f.fmap(g)` must maintain the same type constructor as `f`
/// 6. Parametricity: For any functor `f` and functions `g`, `h`, If `g(x) = h(x)` for all `x`, then `f.fmap(g) = f.fmap(h)`
/// 
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Default, PartialEq, Eq, Debug, Clone)]
/// struct MyType<A>
/// where
///     A: TypeConstraints,
/// {
///     value: A,
/// }
///
/// impl<U> HKT for MyType<U>
/// where
///     U: TypeConstraints,
/// {
///     type Output<T> = MyType<T> where T: TypeConstraints;
/// }
///
/// impl<A> Functor<A> for MyType<A>
/// where
///     A: TypeConstraints,
/// {
///     fn fmap<B, F>(self, f: F) -> Self::Output<B>
///     where
///         B: TypeConstraints,
///         F: FnTrait<A, B>,
///     {
///         MyType { value: f.call(self.value) }
///     }
/// }
///
/// let instance: MyType<i32> = MyType { value: 42 };
/// let new_instance: MyType<String> = instance.fmap(FnType::new(|x: i32| x.to_string()));
/// assert_eq!(new_instance.value, "42".to_string());
/// ```
pub trait Functor<A>: HKT
where
    A: TypeConstraints,
{
    /// Maps a function over the contents of the functor.
    ///
    /// # Type Parameters
    /// * `B` - The type of the resulting functor's contents
    /// * `F` - The type of the mapping function
    ///
    /// # Parameters
    /// * `self` - The functor to map over
    /// * `f` - The function to apply to the functor's contents
    ///
    /// # Returns
    /// A new functor with the function applied to its contents
    ///
    /// # Laws
    /// 1. Identity: `x.fmap(|a| a) == x`
    /// 2. Composition: `x.fmap(|a| f(g(a))) == x.fmap(g).fmap(f)`
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>;
}

impl<T> Functor<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, B>,
    {
        self.into_iter().map(|x| f.call(x)).collect()
    }
}

impl<T> Functor<T> for Box<T>
where
    T: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, B>,
    {
        Box::new(f.call(*self))
    }
}

impl<K, V> Functor<V> for HashMap<K, V>
where
    K: Hash + Eq + Debug + TypeConstraints,
    V: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<V, B>,
    {
        self.into_iter()
            .map(|(k, v)| (k, f.call(v)))
            .collect()
    }
}