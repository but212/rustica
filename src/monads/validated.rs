use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::composable::Composable;
use crate::category::identity::Identity;
use crate::fntype::{FnType, FnTrait};

/// A type that represents a value that can be either valid or invalid
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::monads::validated::{Validated, ValidatedTypeConstraints};
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
/// impl ValidatedTypeConstraints for MyError {}
///
/// let valid: Validated<MyError, i32> = Validated::valid(42);
/// let invalid: Validated<MyError, i32> = Validated::invalid(MyError("Error".to_string()));
///
/// assert_eq!(valid.clone().to_result(), Ok(42));
/// assert_eq!(invalid.clone().to_result(), Err(vec![MyError("Error".to_string())]));
///
/// let result = valid.map_valid(FnType::new(|x| x + 1));
/// assert_eq!(result.to_result(), Ok(43));
///
/// let combined: Validated<MyError, i32> = Validated::valid(1).combine(Validated::valid(2), FnType::new(|x| FnType::new(move |y| x + y)));
/// assert_eq!(combined.to_result(), Ok(3));
/// ```
pub trait ValidatedTypeConstraints: ReturnTypeConstraints + Extend<Self> + IntoIterator<Item = Self> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with a vector of errors of type `E`.
    Invalid(Vec<E>),
}

impl<E, A> Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
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
    /// A `Validated::Invalid` variant containing a vector with the provided error.
    pub fn invalid(e: E) -> Self {
        Validated::Invalid(vec![e])
    }

    /// Creates a new `Validated` instance with multiple invalid values.
    ///
    /// # Arguments
    ///
    /// * `errors` - A vector of error values to be wrapped.
    ///
    /// # Returns
    ///
    /// A `Validated::Invalid` variant containing the provided vector of errors.
    pub fn invalid_vec(errors: Vec<E>) -> Self {
        Validated::Invalid(errors)
    }

    /// Applies a function to the valid value of a `Validated` instance.
    ///
    /// If the `Validated` is `Valid`, it applies the function `f` to the contained value.
    /// If the `Validated` is `Invalid`, it returns the `Invalid` value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The return type of the mapping function, must implement `ReturnTypeConstraints`.
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
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(f)
    }

    /// Applies a function to the invalid value(s) of a `Validated` instance.
    ///
    /// If the `Validated` is `Invalid`, it applies the function `f` to each error in the contained vector.
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
            Validated::Invalid(es) => Validated::Invalid(es.into_iter().map(|e| f.call(e)).collect()),
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
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        E: ValidatedTypeConstraints,
    {
        match (self, other) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call(a).call(b)),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
            (Validated::Invalid(e), _) | (_, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }

    /// Converts the `Validated` instance into a `Result`.
    ///
    /// This method transforms a `Validated<E, A>` into a `Result<A, Vec<E>>`.
    ///
    /// # Returns
    ///
    /// - `Ok(A)` if the `Validated` instance is `Valid`.
    /// - `Err(Vec<E>)` if the `Validated` instance is `Invalid`.
    pub fn to_result(self) -> Result<A, Vec<E>> {
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
    /// * `Validated::Invalid(vec![E])` if the result is `Err(E)`.
    pub fn from_result(result: Result<A, E>) -> Self {
        match result {
            Ok(x) => Validated::Valid(x),
            Err(e) => Validated::Invalid(vec![e]),
        }
    }
}

impl<E, A> Default for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        Validated::Invalid(Default::default())
    }
}

impl<E, A> HKT for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Validated<E, T> where T: ReturnTypeConstraints;
}

impl<E, A> Pure<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(x: A) -> Self::Output<A> {
        Validated::Valid(x)
    }
}

impl<E, A> Functor<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Validated<E, B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f.call(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E, A> Applicative<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, rf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        match (self, rf) {
            (Validated::Valid(x), Validated::Valid(f)) => Validated::Valid(f.call(x)),
            (Validated::Invalid(e1), Validated::Valid(_)) | (Validated::Valid(_), Validated::Invalid(e1)) => Validated::Invalid(e1),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        match (self, mb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f.call((a, b))),
            (Validated::Invalid(e1), Validated::Valid(_)) => Validated::Invalid(e1),
            (Validated::Valid(_), Validated::Invalid(e2)) => Validated::Invalid(e2),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            }
        }
    }

    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        match (self, mb, mc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f.call((a, b, c)))
            }
            (Validated::Invalid(mut e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                e1.extend(e2);
                e1.extend(e3);
                Validated::Invalid(e1)
            }
            (Validated::Invalid(e), _, _) => Validated::Invalid(e),
            (_, Validated::Invalid(e), _) => Validated::Invalid(e),
            (_, _, Validated::Invalid(e)) => Validated::Invalid(e),
        }
    }
}

impl<E, A> Monad<A> for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        match self {
            Validated::Valid(x) => f.call(x),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        A: Into<Self::Output<U>>,
    {
        self.bind(FnType::new(|x: A| x.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x: A| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<E: ValidatedTypeConstraints, A: ReturnTypeConstraints> Identity for Validated<E, A> {}

impl<E: ValidatedTypeConstraints, A: ReturnTypeConstraints> Composable for Validated<E, A> {}

impl<E: ValidatedTypeConstraints, A: ReturnTypeConstraints> Category for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;
}

impl<E: ValidatedTypeConstraints, A: ReturnTypeConstraints> Arrow for Validated<E, A> {}