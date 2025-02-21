use crate::traits::identity::Identity;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::{FnTrait, FnType};

use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;

/// A trait representing functors in category theory.
///
/// Functors are structures that can be mapped over, preserving the structure
/// of the functor while transforming its contents.
///
/// # Type Parameters
/// * `T`: The type of elements contained in the functor.
///
/// # Laws
/// 
/// A Functor instance must satisfy these laws:
/// 
/// 1. Identity: For any functor `f`,
///    `f.fmap(|x| x) = f`
/// 2. Composition: For any functor `f` and functions `g`, `h`,
///    `f.fmap(|x| g(h(x))) = f.fmap(h).fmap(g)`
/// 3. Naturality: For any natural transformation `η` and functor `f`,
///    `η(f.fmap(g)) = η(f).fmap(g)`
/// 4. Type Safety: For `f: F[A]`, `g: A -> B`, then `f.fmap(g): F[B]`
/// 5. Preservation of Structure: `fmap` must preserve the structure of the functor
pub trait Functor<T>: Identity<T>
where
    T: TypeConstraints,
{
    /// Applies a function to the contents of the functor.
    ///
    /// # Type Parameters
    /// * `U`: The resulting type after applying the function.
    /// * `F`: The type of the function to apply.
    ///
    /// # Arguments
    /// * `self`: The functor instance.
    /// * `f`: The function to apply to the functor's contents.
    ///
    /// # Returns
    /// A new functor instance containing the results of applying `f`.
    ///
    /// # Examples
    /// ```
    /// use rustica::prelude::*;
    /// 
    /// #[derive(Default, Clone, PartialEq, Eq)]
    /// struct MyFunctor<T: TypeConstraints>(T);
    /// 
    /// impl<T: TypeConstraints> HKT for MyFunctor<T> {
    ///     type Output<U: TypeConstraints> = MyFunctor<U>;
    /// }
    /// 
    /// impl<T: TypeConstraints> Composable<T> for MyFunctor<T> {
    ///     fn compose_with<U, F>(self, f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(self.0))
    ///     }
    /// }
    /// 
    /// impl<T: TypeConstraints> Identity<T> for MyFunctor<T> {
    ///     fn map_identity<U, F>(f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(T::default()))
    ///     }
    /// }
    /// 
    /// impl<T: TypeConstraints> Functor<T> for MyFunctor<T> {
    ///     fn fmap<U, F>(self, f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(self.0))
    ///     }
    /// }
    /// 
    /// let functor: MyFunctor<i32> = MyFunctor(5);
    /// let result: MyFunctor<i32> = functor.fmap(FnType::new(|x| x * 2));
    /// assert_eq!(result.0, 10);
    /// ```
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>;

    /// Lifts a function to operate on the functor.
    ///
    /// # Type Parameters
    /// * `U`: The resulting type after applying the function.
    /// * `F`: The type of the function to lift.
    ///
    /// # Arguments
    /// * `f`: The function to lift.
    ///
    /// # Returns
    /// A new function that applies `f` to the contents of the functor.
    ///
    /// # Examples
    /// ```
    /// use rustica::prelude::*;
    /// 
    /// #[derive(Default, Clone, PartialEq, Eq)]
    /// struct MyFunctor<T: TypeConstraints>(T);
    /// 
    /// impl<T: TypeConstraints> HKT for MyFunctor<T> {
    ///     type Output<U: TypeConstraints> = MyFunctor<U>;
    /// }
    /// 
    /// impl<T: TypeConstraints> Composable<T> for MyFunctor<T> {
    ///     fn compose_with<U, F>(self, f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(self.0))
    ///     }
    /// }
    /// 
    /// impl<T: TypeConstraints> Identity<T> for MyFunctor<T> {
    ///     fn map_identity<U, F>(f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(T::default()))
    ///     }
    /// }
    /// 
    /// impl<T: TypeConstraints> Functor<T> for MyFunctor<T> {
    ///     fn fmap<U, F>(self, f: F) -> MyFunctor<U>
    ///     where
    ///         U: TypeConstraints,
    ///         F: FnTrait<T, U>,
    ///     {
    ///         MyFunctor(f.call(self.0))
    ///     }
    /// }
    /// 
    /// let double = FnType::new(|x| x * 2);
    /// let lifted_double = MyFunctor::<i32>::lift(double);
    /// let result = lifted_double.call(MyFunctor(5));
    /// assert_eq!(result.0, 10);
    /// ```
    fn lift<U, F>(f: F) -> FnType<Self, Self::Output<U>>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        FnType::new(move |x: Self| x.fmap(f.clone()))
    }
}

impl<T> Functor<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        self.into_iter().map(|x| f.call(x)).collect()
    }
}

impl<T: TypeConstraints> Functor<T> for Box<T> {
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Box::new(f.call(*self))
    }
}

impl<K, V> Functor<V> for HashMap<K, V>
where
    K: Hash + Eq + Debug + TypeConstraints + 'static,
    V: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        self.into_iter()
            .map(|(k, v)| (k, f.call(v)))
            .collect()
    }
}