use crate::traits::functor::Functor;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::{FnType, FnTrait};

/// A trait for comonads, dual to monads.
///
/// # Type Parameters
/// * `T`: The value type within the comonad.
///
/// # Laws
/// 1. Left Identity: `extend(extract)(w) = w`
/// 2. Right Identity: `extract(extend(f)(w)) = f(w)`
/// 3. Associativity: `extend(f)(extend(g)(w)) = extend(|x| f(extend(g)(x)))(w)`
/// 4. Extract-Duplicate Consistency: `extract(duplicate(w)) = w`
/// 5. Duplicate-Extract Consistency: `extend(extract)(duplicate(w)) = duplicate(w)`
/// 
/// # Examples
///
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Clone, Eq, PartialEq, Debug, Default)]
/// struct MyComonad<T> {
///     value: T,
/// }
/// 
/// impl<T> HKT for MyComonad<T> where T: TypeConstraints {
///     type Output<U> = MyComonad<U> where U: TypeConstraints;
/// }
/// 
/// impl<T> Pure<T> for MyComonad<T>
/// where
///     T: TypeConstraints,
/// {
///     fn pure(value: T) -> Self {
///         MyComonad { value }
///     }
/// }
///
/// impl<T> Functor<T> for MyComonad<T>
/// where
///     T: TypeConstraints,
/// {
///     fn fmap<U, F>(self, f: F) -> Self::Output<U>
///     where
///         U: TypeConstraints,
///         F: FnTrait<T, U>,
///     {
///         MyComonad {
///             value: f.call(self.value),
///         }
///     }
/// }
/// 
/// impl<T> Comonad<T> for MyComonad<T>
/// where
///     T: TypeConstraints,
/// {
///     fn extract(&self) -> T {
///         self.value.clone()
///     }
///
///     fn extend<U, F>(self, f: F) -> U
///     where
///         U: TypeConstraints,
///         F: FnTrait<Self, U>,
///     {
///         f.call(self)
///     }
/// }
///
/// let comonad = MyComonad { value: 42 };
/// let extracted_value = comonad.extract();
/// assert_eq!(extracted_value, 42);
///
/// let extended_comonad = comonad.extend(FnType::new(|w: MyComonad<i32>| w.extract() + 1));
/// assert_eq!(extended_comonad, 43);
/// ```
pub trait Comonad<T>: Functor<T> + TypeConstraints
where
    T: TypeConstraints,
{
    /// Extracts a value from a comonad.
    ///
    /// # Returns
    /// The extracted value of type `T`.
    fn extract(&self) -> T;

    /// Extends a comonad by duplicating the context.
    ///
    /// # Arguments
    /// - `self`: The comonad instance.
    /// - `f`: A function that takes a comonad and returns a value of type `U`.
    ///
    /// # Returns
    /// A new comonad containing the result of applying the function `f` to the comonad.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a comonad and returns a value of type `U`.
    fn extend<U, F>(self, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<Self, U>;

    /// Maps a function over a comonad.
    ///
    /// # Arguments
    /// - `self`: The comonad instance.
    /// - `f`: A function that takes a comonad and returns a value of type `U`.
    ///
    /// # Returns
    /// A new comonad containing the result of applying the function `f` to the comonad.
    ///
    /// # Type Parameters
    /// - `U`: The return type of the function `f`.
    /// - `F`: A function type that takes a comonad and returns a value of type `U`.
    fn comap<U, F>(self, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<Self, U>,
    {
        let g = FnType::new(move |w: Self| f.call(w));
        self.extend(g)
    }

    /// Duplicates the context of a comonad.
    ///
    /// # Returns
    /// A new comonad containing the duplicated context.
    fn duplicate(self) -> Self
    where
        Self: Sized,
    {
        self.extend(FnType::new(|w| w))
    }
}

/// A trait for functions that can be used with comonads.
pub trait ComonadFn<T, U, W>
where
    T: TypeConstraints,
    U: TypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Arguments
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U;
}

impl<T, U, W, F> ComonadFn<T, U, W> for F
where
    T: TypeConstraints,
    U: TypeConstraints,
    W: Comonad<T> + Clone + Send + Sync,
    F: Fn(&W) -> U + Clone + Send + Sync,
{
    /// Calls a comonadic function.
    ///
    /// # Arguments
    /// - `self`: The comonadic function instance.
    /// - `w`: The comonad instance.
    ///
    /// # Returns
    /// The result of applying the comonadic function to the comonad.
    fn call_comonadic(&self, w: &W) -> U {
        self(w)
    }
}