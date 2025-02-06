use std::collections::HashMap;
use std::hash::Hash;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::fntype::SendSyncFnTrait;

/// A trait for functors, which are type constructors that can map a function over their contents.
/// # Example
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Default, PartialEq, Eq, Debug, Clone)]
/// struct MyType<A>
/// where
///     A: ReturnTypeConstraints,
/// {
///     value: A,
/// }
///
/// impl<U> HKT for MyType<U>
/// where
///     U: ReturnTypeConstraints,
/// {
///     type Output<T> = MyType<T> where T: ReturnTypeConstraints;
/// }
///
/// impl<A> Functor<A> for MyType<A>
/// where
///     A: ReturnTypeConstraints,
/// {
///     fn map<B, F>(self, f: F) -> Self::Output<B>
///     where
///         B: ReturnTypeConstraints,
///         F: SendSyncFnTrait<A, B>,
///     {
///         MyType { value: f.call(self.value) }
///     }
/// }
///
/// let instance: MyType<i32> = MyType { value: 42 };
/// let new_instance: MyType<String> = instance.map(SendSyncFn::new(|x: i32| x.to_string()));
/// assert_eq!(new_instance.value, "42".to_string());
/// ```
pub trait Functor<A>: HKT
where
    A: ReturnTypeConstraints,
{
    /// Maps a function over the contents of the functor.
    ///
    /// # Parameters
    /// - `self`: The functor instance.
    /// - `f`: A function that takes a value of type `A` and returns a value of type `B`.
    ///
    /// # Returns
    /// A new functor containing the result of applying the function `f` to the contents of the original functor.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `A` and returns a value of type `B`.
    ///
    /// 
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>;
}


impl<T> Functor<T> for Vec<T>
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the contents of the vector.
    ///
    /// # Parameters
    /// - `self`: The vector instance.
    /// - `f`: A function that takes a value of type `T` and returns a value of type `B`.
    ///
    /// # Returns
    /// A new vector containing the result of applying the function `f` to the contents of the original vector.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `T` and returns a value of type `B`.
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, B>,
    {
        self.into_iter().map(|x| f.call(x)).collect()
    }
}

impl<T> Functor<T> for Box<T>
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the contents of the box.
    ///
    /// # Parameters
    /// - `self`: The box instance.
    /// - `f`: A function that takes a value of type `T` and returns a value of type `B`.
    ///
    /// # Returns
    /// A new box containing the result of applying the function `f` to the contents of the original box.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `T` and returns a value of type `B`.
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, B>,
    {
        Box::new(f.call(*self))
    }
}

impl<K, V> Functor<V> for HashMap<K, V>
where
    K: Hash + Eq + ReturnTypeConstraints,
    V: ReturnTypeConstraints,
{
    /// Maps a function over the contents of the hashmap.
    ///
    /// # Parameters
    /// - `self`: The hashmap instance.
    /// - `f`: A function that takes a value of type `V` and returns a value of type `B`.
    ///
    /// # Returns
    /// A new hashmap containing the result of applying the function `f` to the contents of the original hashmap.
    ///
    /// # Type Parameters
    /// - `B`: The return type of the function `f`.
    /// - `F`: A function type that takes a value of type `V` and returns a value of type `B`.
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<V, B>,
    {
        self.into_iter()
            .map(|(k, v)| (k, f.call(v)))
            .collect()
    }
}
