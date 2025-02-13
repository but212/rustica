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
/// # Type Parameters
/// * `E` - The error type, must be a collection type that can extend itself
/// * `A` - The valid value type
///
/// # Laws
/// A Validated instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Error Accumulation: For invalid values `v1` and `v2`,
///    `v1.combine(v2, f)` must contain all errors from both `v1` and `v2`
/// 2. Valid Combination: For valid values `v1` and `v2`,
///    `v1.combine(v2, f) = Validated::Valid(f(v1.value)(v2.value))`
/// 3. Invalid Priority: For valid value `v1` and invalid value `v2`,
///    `v1.combine(v2, f)` must be invalid with `v2`'s errors
/// 4. Result Consistency: For any Validated value `v`,
///    `Validated::from_result(v.to_result()) = v`
/// 5. Invalid Map Independence: For invalid value `v` and function `f`,
///    `v.map_valid(f)` must preserve all original errors
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::monads::validated::{Validated, ValidatedTypeConstraints};
/// use rustica::fntype::{FnType, FnTrait};
///
/// #[derive(Hash, Debug, Clone, PartialEq, Eq, Default)]
/// struct MyError(String);
///
/// // Implementing the Extend trait for MyError
/// impl Extend<MyError> for MyError {
///     fn extend<T: IntoIterator<Item = MyError>>(&mut self, iter: T) {
///         for item in iter {
///             self.0.push_str(&item.0);
///         }
///     }
/// }
///
/// // Implementing the IntoIterator trait for MyError
/// impl IntoIterator for MyError {
///     type Item = MyError;
///     type IntoIter = std::vec::IntoIter<MyError>;
///
///     fn into_iter(self) -> Self::IntoIter {
///         vec![self].into_iter()
///     }
/// }
///
/// impl ValidatedTypeConstraints for MyError {}
///
/// let valid_value: Validated<MyError, i32> = Validated::valid(42);
/// let invalid_value: Validated<MyError, i32> = Validated::invalid(MyError("Error".to_string()));
///
/// assert_eq!(valid_value.clone().to_result(), Ok(42));
/// assert_eq!(invalid_value.clone().to_result(), Err(vec![MyError("Error".to_string())]));
///
/// let result = valid_value.map_valid(FnType::new(|x| x + 1));
/// assert_eq!(result.to_result(), Ok(43));
///
/// let combined_result: Validated<MyError, i32> = Validated::valid(1).combine(Validated::valid(2), FnType::new(|x| FnType::new(move |y| x + y)));
/// assert_eq!(combined_result.to_result(), Ok(3));
/// ```

pub trait ValidatedTypeConstraints: ReturnTypeConstraints + Extend<Self> + IntoIterator<Item = Self> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    Valid(A),
    Invalid(Vec<E>),
}

impl<E, A> Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new valid value
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid value
    pub fn invalid(e: E) -> Self {
        let mut errors = Vec::new();
        errors.extend(std::iter::once(e));
        Validated::Invalid(errors)
    }

    /// Creates a new invalid value from a vector of errors
    pub fn invalid_vec(errors: Vec<E>) -> Self {
        Validated::Invalid(errors)
    }

    /// Maps a function over the valid value
    pub fn map_valid<B, F>(self, f: F) -> Validated<E, B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(f)
    }

    /// Maps a function over the invalid value
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

    /// Combines two validated values using a function
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

    /// Converts to a Result
    pub fn to_result(self) -> Result<A, Vec<E>> {
        match self {
            Validated::Valid(x) => Ok(x),
            Validated::Invalid(e) => Err(e),
        }
    }

    /// Creates from a Result
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

impl<E, A> Identity for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<E, A> Composable for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<E, A> Category for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        FnType::new(|x| x)
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<E, A> Arrow for Validated<E, A>
where
    E: ValidatedTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        FnType::new(move |x| f.call(x))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        FnType::new(move |(x, y)| (f.call(x), y))
    }
}