#![doc = include_str!("../../../docs/datatypes/validated_core.md")]

use crate::traits::semigroup::Semigroup;
use alloc::vec;
use alloc::vec::Vec;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

/// Non-empty collection of validation errors backed by a private `Vec`.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[repr(transparent)]
pub struct NonEmptyErrors<E>(Vec<E>);

impl<E> NonEmptyErrors<E> {
    pub fn new(first: E) -> Self {
        Self(vec![first])
    }

    pub(crate) fn try_from_vec(errors: Vec<E>) -> Option<Self> {
        (!errors.is_empty()).then_some(Self(errors))
    }

    /// Creates a non-empty error collection from an iterator, or `None` if empty.
    pub fn try_from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = iter.into_iter();
        let first = iter.next()?;
        Some(Self::from_first_and_iter(first, iter))
    }

    pub(crate) fn from_first_and_iter<I>(first: E, rest: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let rest_iter = rest.into_iter();
        let (lower, _) = rest_iter.size_hint();
        let mut errors = Vec::with_capacity(1 + lower);
        errors.push(first);
        errors.extend(rest_iter);
        Self(errors)
    }

    pub(crate) fn map<F, G>(self, f: G) -> NonEmptyErrors<F>
    where
        G: FnMut(E) -> F,
    {
        NonEmptyErrors(self.0.into_iter().map(f).collect())
    }

    pub fn try_from_slice(slice: &[E]) -> Option<Self>
    where
        E: Clone,
    {
        (!slice.is_empty()).then_some(Self(slice.to_vec()))
    }

    /// Converts into a `Vec<E>`.
    #[must_use]
    pub fn into_vec(self) -> Vec<E> {
        self.0
    }

    /// Returns a slice of the errors.
    #[must_use]
    pub const fn as_slice(&self) -> &[E] {
        self.0.as_slice()
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Always returns `false`.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        false
    }

    pub fn push(&mut self, error: E) {
        self.0.push(error);
    }

    pub fn extend<I: IntoIterator<Item = E>>(&mut self, errors: I) {
        self.0.extend(errors);
    }

    /// Combines multiple non-empty error collections in encounter order,
    /// pre-reserving capacity in a single reallocation.
    pub(crate) fn combine_multiple<const N: usize>(collections: [Option<Self>; N]) -> Option<Self> {
        let total: usize = collections.iter().flatten().map(Self::len).sum();
        let mut it = collections.into_iter().flatten();
        let first = it.next()?;

        let mut base = first.into_vec();
        if total > base.len() {
            base.reserve(total - base.len());
        }
        for es in it {
            base.extend(es);
        }

        // Safety/Invariant: `first` is a non-empty collection, so `base` is guaranteed non-empty.
        Some(Self(base))
    }
}

impl<E> core::ops::Deref for NonEmptyErrors<E> {
    type Target = [E];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<E> core::ops::DerefMut for NonEmptyErrors<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut_slice()
    }
}

impl<E: PartialEq> PartialEq<[E]> for NonEmptyErrors<E> {
    fn eq(&self, other: &[E]) -> bool {
        self.as_slice() == other
    }
}

impl<E: PartialEq> PartialEq<&[E]> for NonEmptyErrors<E> {
    fn eq(&self, other: &&[E]) -> bool {
        self.as_slice() == *other
    }
}

impl<E: PartialEq> PartialEq<Vec<E>> for NonEmptyErrors<E> {
    fn eq(&self, other: &Vec<E>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E: PartialEq, const N: usize> PartialEq<[E; N]> for NonEmptyErrors<E> {
    fn eq(&self, other: &[E; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E> Semigroup for NonEmptyErrors<E> {
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<E> IntoIterator for NonEmptyErrors<E> {
    type Item = E;
    type IntoIter = alloc::vec::IntoIter<E>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Formats errors in encounter order separated by `"; "`.
impl<E: core::fmt::Display> core::fmt::Display for NonEmptyErrors<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for (i, err) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str("; ")?;
            }
            write!(f, "{err}")?;
        }
        Ok(())
    }
}

/// Error implementation for accumulated validation errors.
///
/// `source` returns `None` because accumulated errors are peer failures, not a causal chain.
impl<E: core::fmt::Debug + core::fmt::Display + core::error::Error + 'static> core::error::Error
    for NonEmptyErrors<E>
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        None
    }
}

#[cfg(feature = "serde")]
impl<E: serde::Serialize> serde::Serialize for NonEmptyErrors<E> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, E: serde::Deserialize<'de>> serde::Deserialize<'de> for NonEmptyErrors<E> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let errors = Vec::<E>::deserialize(deserializer)?;
        if errors.is_empty() {
            return Err(serde::de::Error::custom("Validated errors cannot be empty"));
        }
        Ok(Self(errors))
    }
}

/// Accumulates validation errors instead of failing fast.
///
/// Represents either a valid value `T` or non-empty errors `NonEmptyErrors<E>`.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Validated<T, E> {
    /// Valid value.
    Valid(T),
    /// One or more validation errors.
    Invalid(NonEmptyErrors<E>),
}

impl<T, E> Validated<T, E> {
    /// Returns `true` if valid.
    pub const fn is_valid(&self) -> bool {
        matches!(self, Self::Valid(_))
    }

    /// Returns `true` if invalid.
    pub const fn is_invalid(&self) -> bool {
        !self.is_valid()
    }

    /// Creates a valid instance.
    pub const fn valid(x: T) -> Self {
        Self::Valid(x)
    }

    /// Creates an invalid instance with a single error.
    pub fn invalid(e: E) -> Self {
        Self::Invalid(NonEmptyErrors::new(e))
    }

    /// Creates an invalid instance from an error collection.
    ///
    /// # Panics
    ///
    /// Panics if `errors` is empty.
    pub fn invalid_many<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        Self::try_invalid_many(errors).expect("Validated::invalid_many requires at least one error")
    }

    /// Creates an invalid instance from an iterator, or `None` if empty.
    pub fn try_invalid_many<I>(errors: I) -> Option<Self>
    where
        I: IntoIterator<Item = E>,
    {
        NonEmptyErrors::try_from_iter(errors).map(Validated::Invalid)
    }

    /// Returns `Ok(T)` if valid, or `Err(NonEmptyErrors<E>)` if invalid.
    ///
    /// # Errors
    ///
    /// Returns `Err(NonEmptyErrors<E>)` containing all accumulated errors when `self` is [`Invalid`](Self::Invalid).
    pub fn into_value(self) -> Result<T, NonEmptyErrors<E>> {
        match self {
            Self::Valid(a) => Ok(a),
            Self::Invalid(es) => Err(es),
        }
    }

    /// Returns `Ok(NonEmptyErrors<E>)` if invalid, or `Err(T)` if valid.
    ///
    /// # Errors
    ///
    /// Returns `Err(T)` containing the valid value when `self` is [`Valid`](Self::Valid).
    pub fn into_error_payload(self) -> Result<NonEmptyErrors<E>, T> {
        match self {
            Self::Valid(a) => Err(a),
            Self::Invalid(es) => Ok(es),
        }
    }

    pub(crate) fn into_error_opt(self) -> Option<NonEmptyErrors<E>> {
        match self {
            Self::Valid(_) => None,
            Self::Invalid(es) => Some(es),
        }
    }

    /// Returns the inner value.
    ///
    /// # Panics
    ///
    /// Panics if invalid.
    pub fn unwrap(self) -> T
    where
        E: core::fmt::Debug,
    {
        match self {
            Self::Valid(value) => value,
            Self::Invalid(e) => {
                panic!("Called Validated::unwrap() on an Invalid value: {e:?}")
            },
        }
    }

    /// Returns the inner value or `default`.
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Self::Valid(x) => x,
            Self::Invalid(_) => default,
        }
    }

    /// Returns the error collection.
    ///
    /// # Panics
    ///
    /// Panics if valid.
    pub fn unwrap_invalid(self) -> NonEmptyErrors<E>
    where
        T: core::fmt::Debug,
    {
        match self {
            Self::Invalid(es) => es,
            Self::Valid(a) => {
                panic!("Called Validated::unwrap_invalid() on a Valid value: {a:?}")
            },
        }
    }

    /// Returns `Some(&T)` if valid, otherwise `None`.
    pub const fn as_option(&self) -> Option<&T> {
        match self {
            Self::Valid(x) => Some(x),
            Self::Invalid(_) => None,
        }
    }

    /// Converts into `Some(T)` if valid, otherwise `None`.
    pub fn into_option(self) -> Option<T> {
        match self {
            Self::Valid(x) => Some(x),
            Self::Invalid(_) => None,
        }
    }

    /// Converts into `Result`, discarding all but the first error if invalid.
    ///
    /// # Errors
    ///
    /// Returns `Err(E)` containing the first error when `self` is [`Invalid`](Self::Invalid).
    ///
    /// # Panics
    ///
    /// Never panics; `NonEmptyErrors` is statically guaranteed to contain at least one error.
    pub fn into_result_first_error(self) -> Result<T, E> {
        match self {
            Self::Valid(value) => Ok(value),
            Self::Invalid(errors) => Err(errors
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }

    /// Converts `Some(value)` to `Valid(value)` and `None` to `invalid(error)`.
    pub fn from_option(option: Option<T>, error: E) -> Self {
        Self::from_option_with(option, move || error)
    }

    /// Converts `Some(value)` to `Valid(value)` and `None` to `invalid(error_fn())`.
    pub fn from_option_with<F>(option: Option<T>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error_fn()),
        }
    }
}

impl<T, E> From<Result<T, E>> for Validated<T, E> {
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(value) => Self::Valid(value),
            Err(error) => Self::invalid(error),
        }
    }
}

impl<T: Clone, E: Clone> From<&Result<T, E>> for Validated<T, E> {
    fn from(result: &Result<T, E>) -> Self {
        result.clone().into()
    }
}

/// Combines two `Validated` values: merges values via `T::combine` if both valid,
/// preserves errors if one is invalid, or concatenates errors if both invalid.
impl<T: Semigroup, E> Semigroup for Validated<T, E> {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Valid(a1), Self::Valid(a2)) => Self::Valid(a1.combine(a2)),
            (Self::Valid(_), o @ Self::Invalid(_)) => o,
            (s @ Self::Invalid(_), Self::Valid(_)) => s,
            (Self::Invalid(e1), Self::Invalid(e2)) => Self::Invalid(e1.combine(e2)),
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<T, E> Arbitrary for Validated<T, E>
where
    T: Arbitrary,
    E: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = T::arbitrary(g);
        let y = E::arbitrary(g);
        if bool::arbitrary(g) {
            Self::valid(x)
        } else {
            Self::invalid(y)
        }
    }
}

#[cfg(test)]
#[allow(clippy::missing_panics_doc)]
mod tests {
    use alloc::string::{String, ToString};

    use super::*;

    #[test]
    fn non_empty_errors_fallible_construction() {
        assert_eq!(NonEmptyErrors::<String>::try_from_iter(Vec::new()), None);

        let errors = NonEmptyErrors::try_from_iter(["first".to_string(), "second".to_string()])
            .expect("non-empty input should construct errors");
        assert_eq!(errors.as_slice(), ["first", "second"]);
    }

    #[test]
    fn test_value_and_error_extraction() {
        let valid: Validated<i32, &str> = Validated::valid(42);
        assert_eq!(valid.clone().into_value(), Ok(42));
        assert_eq!(valid.into_error_payload(), Err(42));

        let invalid: Validated<i32, &str> = Validated::invalid("err");
        assert_eq!(
            invalid.clone().into_value(),
            Err(NonEmptyErrors::new("err"))
        );
        assert_eq!(invalid.into_error_payload(), Ok(NonEmptyErrors::new("err")));
    }

    #[test]
    fn test_non_empty_errors_contracts() {
        let errors = NonEmptyErrors::new("first".to_string());
        let vec_out: Vec<String> = errors.clone().into_vec();
        assert_eq!(vec_out, vec!["first".to_string()]);

        // PartialEq contracts
        assert_eq!(errors, vec!["first".to_string()]);
        assert_eq!(errors, ["first".to_string()][..]);
        assert_eq!(errors, &["first".to_string()][..]);
        assert_eq!(errors, ["first".to_string()]);

        // Semigroup contract
        let other = NonEmptyErrors::new("second".to_string());
        let combined = errors.combine(other);
        assert_eq!(combined.as_slice(), &["first", "second"]);

        // try_from_slice contract
        let slice = ["a", "b"];
        let from_slice = NonEmptyErrors::try_from_slice(&slice).unwrap();
        assert_eq!(from_slice.as_slice(), &["a", "b"]);
        assert_eq!(NonEmptyErrors::<&str>::try_from_slice(&[]), None);
    }

    #[test]
    fn test_non_empty_errors_deref_mut() {
        let mut errors = NonEmptyErrors::new("a".to_string());
        errors.push("b".to_string());
        assert_eq!(errors.len(), 2);

        // Mutate via DerefMut slice indexing
        errors[0].make_ascii_uppercase();
        errors[1].make_ascii_uppercase();
        assert_eq!(errors.as_slice(), &["A", "B"]);
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap() on an Invalid value:")]
    fn unwrap_rejects_invalid_values() {
        Validated::<i32, &str>::invalid("error").unwrap();
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap_invalid() on a Valid value:")]
    fn unwrap_invalid_rejects_valid_values() {
        Validated::<i32, &str>::valid(42).unwrap_invalid();
    }

    #[test]
    fn test_option_and_result_conversions() {
        let valid: Validated<i32, &str> = Ok(42).into();
        assert_eq!(valid.as_option(), Some(&42));
        assert_eq!(valid.clone().into_option(), Some(42));
        assert_eq!(valid.as_option().copied(), Some(42));
        assert_eq!(valid.into_result_first_error(), Ok(42));

        let res: Result<i32, &str> = Err("err");
        let invalid = Validated::from(&res);
        assert_eq!(invalid.as_option(), None);
        assert_eq!(invalid.into_result_first_error(), Err("err"));

        let from_some = Validated::from_option(Some(10), "err");
        assert_eq!(from_some, Validated::valid(10));
        let from_none: Validated<i32, &str> = Validated::from_option_with(None, || "dynamic_err");
        assert_eq!(from_none, Validated::invalid("dynamic_err"));
    }

    #[test]
    fn test_const_fn_capability() {
        const fn inspect_errors<E>(errs: &NonEmptyErrors<E>) -> (&[E], usize, bool) {
            (errs.as_slice(), errs.len(), errs.is_empty())
        }

        const fn inspect_validated<T, E>(v: &Validated<T, E>) -> (bool, bool, Option<&T>) {
            (v.is_valid(), v.is_invalid(), v.as_option())
        }

        let errors = NonEmptyErrors::new("err");
        let (slice, len, is_empty) = inspect_errors(&errors);
        assert_eq!(slice, &["err"]);
        assert_eq!(len, 1);
        assert!(!is_empty);

        let valid: Validated<i32, &str> = Validated::valid(42);
        let (is_valid, is_invalid, opt) = inspect_validated(&valid);
        assert!(is_valid);
        assert!(!is_invalid);
        assert_eq!(opt, Some(&42));
    }

    #[test]
    fn test_non_empty_errors_display_and_error() {
        #[derive(Debug)]
        struct DummyError(&'static str);
        impl core::fmt::Display for DummyError {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}", self.0)
            }
        }
        impl core::error::Error for DummyError {}

        let errors = NonEmptyErrors::from_first_and_iter(
            "first error".to_string(),
            ["second error".to_string(), "third error".to_string()],
        );
        assert_eq!(
            alloc::format!("{errors}"),
            "first error; second error; third error"
        );

        let err_col = NonEmptyErrors::new(DummyError("inner root"));
        let as_error: &dyn core::error::Error = &err_col;
        assert_eq!(alloc::format!("{err_col}"), "inner root");
        // Validation errors are peers rather than a causal chain, so source is None.
        assert!(as_error.source().is_none());
    }
}
