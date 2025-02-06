use crate::category::functor::Functor;
use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::{SendSyncFn, SendSyncFnTrait};

/// A comonad is the categorical dual of a monad. While a monad adds a layer of context
/// to values, a comonad extracts values from a context.
///
/// # Type Parameters
/// * `T` - The type of value contained in the comonad
///
/// # Laws
/// A comonad must satisfy these laws:
/// 1. Left Identity: `extract(duplicate(w)) = w`
/// 2. Right Identity: `duplicate(extract(w)) = w`
/// 3. Associativity: `map(duplicate)(duplicate(w)) = duplicate(duplicate(w))`
/// 4. Extension Identity: `extend(extract)(w) = w`
/// 5. Extension Composition: `extend(f)(extend(g)(w)) = extend(x -> f(extend(g)(x)))(w)`
/// 6. Comonad Map-Extend: `map(f)(w) = extend(x -> f(extract(x)))(w)`
///
/// # Examples
///
/// ```
/// use rustica::category::comonad::Comonad;
/// use rustica::prelude::*;
///
/// #[derive(Clone, Eq, PartialEq, Debug, Default)]
/// struct MyComonad<T> {
///     value: T,
/// }
/// 
/// impl<T> HKT for MyComonad<T> where T: ReturnTypeConstraints {
///     type Output<U> = MyComonad<U> where U: ReturnTypeConstraints;
/// }
/// 
/// impl<T> Pure<T> for MyComonad<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn pure(value: T) -> Self {
///         MyComonad { value }
///     }
/// }
///
/// impl<T> Functor<T> for MyComonad<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn map<U, F>(self, f: F) -> Self::Output<U>
///     where
///         U: ReturnTypeConstraints,
///         F: SendSyncFnTrait<T, U>,
///     {
///         MyComonad {
///             value: f.call(self.value),
///         }
///     }
/// }
/// 
/// impl<T> Comonad<T> for MyComonad<T>
/// where
///     T: ReturnTypeConstraints,
/// {
///     fn extract(&self) -> T {
///         self.value.clone()
///     }
///
///     fn extend<U, F>(self, f: F) -> U
///     where
///         U: ReturnTypeConstraints,
///         F: SendSyncFnTrait<Self, U>,
///     {
///         f.call(self)
///     }
/// }
///
/// let comonad = MyComonad { value: 42 };
/// let extracted_value = comonad.extract();
/// assert_eq!(extracted_value, 42);
///
/// let extended_comonad = comonad.extend(SendSyncFn::new(|w: MyComonad<i32>| w.extract() + 1));
/// assert_eq!(extended_comonad, 43);
/// ```
pub trait Comonad<T>: Functor<T> + ReturnTypeConstraints
where
    T: ReturnTypeConstraints,
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
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<Self, U>;

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
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<Self, U>,
    {
        let g = SendSyncFn::new(move |w: Self| f.call(w));
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
        self.extend(SendSyncFn::new(|w| w))
    }
}

/// A trait for functions that can be used with comonads.
pub trait ComonadFn<T, U, W>
where
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
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
    T: ReturnTypeConstraints,
    U: ReturnTypeConstraints,
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