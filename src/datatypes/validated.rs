use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::fntype::{FnType, FnTrait};
use crate::traits::semigroup::Semigroup;

/// A type that represents a value that can be either valid or invalid
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::datatypes::validated::{Validated, ValidatedTypeConstraints};
/// use rustica::fntype::{FnType, FnTrait};
///
/// #[derive(Debug, Clone, PartialEq, Eq, Default)]
/// struct MyError(String);
///
/// impl Extend<MyError> for MyError {
///     fn extend<T: IntoIterator<Item = MyError>>(&mut self, iter: T) {
///         for item in iter {
///             self.0.push_str(&item.0);
///         }
///     }
/// }
///
/// impl IntoIterator for MyError {
///     type Item = MyError;
///     type IntoIter = std::vec::IntoIter<Self>;
///     fn into_iter(self) -> Self::IntoIter { vec![self].into_iter() }
/// }
///
/// impl Semigroup<MyError> for MyError {
///     fn combine(mut self, other: Self) -> Self {
///         self.0.push_str(&other.0);
///         self
///     }
/// }
///
/// impl ValidatedTypeConstraints for MyError {}
///
/// let valid: Validated<MyError, i32> = Validated::valid(42);
/// let invalid: Validated<MyError, i32> = Validated::invalid(MyError("Error".to_string()));
///
/// assert_eq!(valid.clone().to_result(), Ok(42));
/// assert_eq!(invalid.clone().to_result(), Err(MyError("Error".to_string())));
///
/// let result = valid.map_valid(FnType::new(|x| x + 1));
/// assert_eq!(result.to_result(), Ok(43));
///
/// let combined: Validated<MyError, i32> = Validated::valid(1).combine(Validated::valid(2), FnType::new(|x| FnType::new(move |y| x + y)));
/// assert_eq!(combined.to_result(), Ok(3));
/// ```
pub trait ValidatedTypeConstraints: TypeConstraints + Extend<Self> + IntoIterator<Item = Self> + Semigroup<Self> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Validated<E: ValidatedTypeConstraints, A: TypeConstraints> {
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with a value of type `E`.
    Invalid(E),
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Validated<E, A> {
    /// Creates a new `Validated` instance with a valid value.
    ///
    /// # Arguments
    ///
    /// * `x` - The valid value to be wrapped.
    ///
    /// # Returns
    ///
    /// A `Validated::Valid` variant containing the provided value.
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new `Validated` instance with an invalid value.
    ///
    /// # Arguments
    ///
    /// * `e` - The error value to be wrapped.
    ///
    /// # Returns
    ///
    /// A `Validated::Invalid` variant containing the provided error.
    pub fn invalid(e: E) -> Self {
        Validated::Invalid(e)
    }

    /// Applies a function to the valid value of a `Validated` instance.
    ///
    /// If the `Validated` is `Valid`, it applies the function `f` to the contained value.
    /// If the `Validated` is `Invalid`, it returns the `Invalid` value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The return type of the mapping function, must implement `TypeConstraints`.
    /// * `F`: The mapping function type, must implement `FnTrait<A, B>`.
    ///
    /// # Arguments
    ///
    /// * `self`: The `Validated` instance to map over.
    /// * `f`: The function to apply to the valid value.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance with the mapped value if valid, or the original errors if invalid.
    pub fn map_valid<B, F>(self, f: F) -> Validated<E, B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(f)
    }

    /// Applies a function to the invalid value(s) of a `Validated` instance.
    ///
    /// If the `Validated` is `Invalid`, it applies the function `f` to each error in the contained value.
    /// If the `Validated` is `Valid`, it returns the `Valid` value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The new error type, must implement `ValidatedTypeConstraints`.
    /// * `F`: The mapping function type, must implement `FnTrait<E, G>`.
    ///
    /// # Arguments
    ///
    /// * `self`: The `Validated` instance to map over.
    /// * `f`: The function to apply to each invalid value.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance with the mapped errors if invalid, or the original value if valid.
    pub fn map_invalid<G, F>(self, f: F) -> Validated<G, A>
    where
        G: ValidatedTypeConstraints,
        F: FnTrait<E, G>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(e) => Validated::Invalid(f.call(e)),
        }
    }

    /// Combines two `Validated` instances using a provided function.
    ///
    /// This method combines the current `Validated` instance with another one,
    /// applying the provided function `f` if both are valid. If either is invalid,
    /// it collects all errors.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the value in the other `Validated` instance.
    /// * `C`: The return type of the combining function.
    /// * `F`: The type of the combining function.
    ///
    /// # Arguments
    ///
    /// * `self`: The current `Validated` instance.
    /// * `other`: Another `Validated` instance to combine with.
    /// * `f`: A function that takes the value from `self` and returns a function
    ///        that takes the value from `other` and returns a new value.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance containing either:
    /// - A `Valid` value if both inputs were valid, with the result of applying `f`.
    /// - An `Invalid` value containing all errors if either input was invalid.
    pub fn combine<B, C, F>(self, other: Validated<E, B>, f: F) -> Validated<E, C>
    where
        F: FnTrait<A, FnType<B, C>>,
        B: TypeConstraints,
        C: TypeConstraints,
        E: ValidatedTypeConstraints,
    {
        match (self, other) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call(a).call(b)),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                Validated::Invalid(e1.combine(e2))
            }
            (Validated::Invalid(e), _) | (_, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }

    /// Converts the `Validated` instance into a `Result`.
    ///
    /// This method transforms a `Validated<E, A>` into a `Result<A, E>`.
    ///
    /// # Returns
    ///
    /// - `Ok(A)` if the `Validated` instance is `Valid`.
    /// - `Err(E)` if the `Validated` instance is `Invalid`.
    pub fn to_result(self) -> Result<A, E> {
        match self {
            Validated::Valid(x) => Ok(x),
            Validated::Invalid(e) => Err(e),
        }
    }

    /// Converts a `Result` into a `Validated`.
    ///
    /// # Arguments
    ///
    /// * `result` - A `Result<A, E>` to convert.
    ///
    /// # Returns
    ///
    /// * `Validated::Valid(A)` if the result is `Ok(A)`.
    /// * `Validated::Invalid(E)` if the result is `Err(E)`.
    pub fn from_result(result: Result<A, E>) -> Self {
        match result {
            Ok(x) => Validated::Valid(x),
            Err(e) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Default for Validated<E, A> {
    fn default() -> Self {
        Validated::Invalid(Default::default())
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> HKT for Validated<E, A> {
    type Output<T> = Validated<E, T> where T: TypeConstraints;
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Pure<A> for Validated<E, A> {
    fn pure(x: A) -> Self::Output<A> {
        Validated::Valid(x)
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Functor<A> for Validated<E, A> {
    fn fmap<B, F>(self, f: F) -> Validated<E, B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f.call(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Applicative<A> for Validated<E, A> {
    fn apply<B, F>(self, rf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        match (self, rf) {
            (Validated::Valid(x), Validated::Valid(f)) => Validated::Valid(f.call(x)),
            (Validated::Invalid(e1), Validated::Valid(_)) | (Validated::Valid(_), Validated::Invalid(e1)) => Validated::Invalid(e1),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.combine(e2)),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        match (self, mb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call((a, b))),
            (Validated::Invalid(e1), Validated::Valid(_)) => Validated::Invalid(e1),
            (Validated::Valid(_), Validated::Invalid(e2)) => Validated::Invalid(e2),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.combine(e2)),
        }
    }

    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        match (self, mb, mc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f.call((a, b, c)))
            }
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let e = e1.combine(e2).combine(e3);
                Validated::Invalid(e)
            }
            (Validated::Invalid(e), _, _) => Validated::Invalid(e),
            (_, Validated::Invalid(e), _) => Validated::Invalid(e),
            (_, _, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Identity<A> for Validated<E, A> {
    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<A, U>,
    {
        Validated::Valid(f.call(A::default()))
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Composable<A> for Validated<E, A> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<A, U>,
    {
        match self {
            Validated::Valid(a) => Validated::Valid(f.call(a)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Category<A> for Validated<E, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Monad<A> for Validated<E, A> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        match self {
            Validated::Valid(a) => f.call(a),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        match self {
            Validated::Valid(a) => a.into(),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn then<B: TypeConstraints>(self, mb: Self::Output<B>) -> Self::Output<B> {
        match (self, mb) {
            (Validated::Valid(_), b) => b,
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.combine(e2)),
            (Validated::Invalid(e), _) => Validated::Invalid(e),
        }
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        match self {
            Validated::Valid(a) => Validated::Valid(f.call(a)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeConstraints, A: TypeConstraints> Arrow<A, A> for Validated<E, A> {}