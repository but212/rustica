use std::sync::Arc;
use crate::traits::{
    hkt::{HKT, AnyBox, TypeOps},
    functor::Functor,
    bifunctor::Bifunctor,
    semigroup::Semigroup,
    monoid::Monoid,
    pure::Pure,
    applicative::Applicative,
    monad::Monad,
    identity::Identity,
};

pub trait ValidatedTypeOps: TypeOps + Semigroup + Monoid + Clone + PartialEq + 'static {}

impl<T: TypeOps + Semigroup + Monoid + Clone + PartialEq + 'static> ValidatedTypeOps for T {}

/// Represents a value that can be either valid or invalid.
///
/// This type is useful for accumulating errors, especially in the context of form validation
/// or data processing where multiple errors might occur.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::validated::Validated;
///
/// fn validate_age(age: i32) -> Validated<String, i32> {
///     if age >= 0 && age <= 150 {
///         Validated::new_valid(age)
///     } else {
///         Validated::new_invalid("Age must be between 0 and 150".to_string())
///     }
/// }
///
/// let valid_age = validate_age(25);
/// let invalid_age = validate_age(200);
///
/// assert_eq!(valid_age, Validated::Valid(25));
/// assert_eq!(invalid_age, Validated::Invalid("Age must be between 0 and 150".to_string()));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Validated<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> {
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with a value of type `E`.
    Invalid(E),
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Validated<E, A> {
    /// Constructs a new `Validated` instance with a valid value.
    ///
    /// # Arguments
    ///
    /// * `value` - The valid value to be wrapped.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance containing the valid value.
    pub fn new_valid(value: A) -> Self {
        Self::Valid(value)
    }

    /// Constructs a new `Validated` instance with an invalid value.
    ///
    /// # Arguments
    ///
    /// * `error` - The error value to be wrapped.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance containing the invalid value.
    pub fn new_invalid(error: E) -> Self {
        Self::Invalid(error)
    }

    /// Maps a function over the valid value, if present.
    ///
    /// # Arguments
    ///
    /// * `f` - The function to apply to the valid value.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance with the function applied to the valid value, if present.
    pub fn map_valid<F: FnOnce(A) -> B, B: TypeOps + Clone + Default + PartialEq + 'static>(self, f: F) -> Validated<E, B> {
        match self {
            Validated::Valid(a) => Validated::Valid(f(a)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    /// Maps a function over the invalid value, if present.
    ///
    /// # Arguments
    ///
    /// * `f` - The function to apply to the invalid value.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance with the function applied to the invalid value, if present.
    pub fn map_invalid<F: FnOnce(E) -> G, G: ValidatedTypeOps>(self, f: F) -> Validated<G, A> {
        match self {
            Validated::Valid(a) => Validated::Valid(a),
            Validated::Invalid(e) => Validated::Invalid(f(e)),
        }
    }

    /// Converts a `Result` into a `Validated` instance.
    ///
    /// # Arguments
    ///
    /// * `result` - The `Result` to convert.
    ///
    /// # Returns
    ///
    /// A new `Validated` instance based on the input `Result`.
    pub fn from_result(result: Result<A, E>) -> Self {
        match result {
            Ok(a) => Validated::Valid(a),
            Err(e) => Validated::Invalid(e),
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> HKT for Validated<E, A> {
    fn apply_type(&self) -> AnyBox {
        match self {
            Validated::Valid(a) => a.clone_box(),
            Validated::Invalid(e) => e.clone_box(),
        }
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Self>().map(|x| Arc::new(x.clone()) as AnyBox)
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Identity for Validated<E, A> {
    fn identity() -> AnyBox {
        Arc::new(Validated::<E, A>::Valid(A::default())) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Functor for Validated<E, A> {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(a) => f(a.clone_box()),
            Validated::Invalid(e) => e.clone_box(),
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Pure for Validated<E, A> {
    fn pure(a: AnyBox) -> AnyBox {
        if let Some(value) = a.downcast_ref::<A>() {
            Arc::new(Validated::<E, A>::Valid(value.clone()))
        } else {
            panic!("Failed to downcast to A in pure")
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Bifunctor for Validated<E, A> {
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(a) => f(a.clone_box()),
            Validated::Invalid(e) => g(e.clone_box()),
        }
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(a) => f(a.clone_box()),
            Validated::Invalid(e) => e.clone_box(),
        }
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(a) => a.clone_box(),
            Validated::Invalid(e) => f(e.clone_box()),
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Semigroup for Validated<E, A> {
    fn combine(&self, other: AnyBox) -> AnyBox {
        if let Some(other) = other.downcast_ref::<Self>() {
            match (self, other) {
                (Validated::Valid(a), Validated::<E, A>::Valid(_)) => Arc::new(Validated::<E, A>::Valid(a.clone())),
                (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                    let combined = e1.combine(Arc::new(e2.clone()) as AnyBox);
                    if let Some(e) = combined.downcast_ref::<E>() {
                        Arc::new(Validated::<E, A>::Invalid(e.clone()))
                    } else {
                        Arc::new(Validated::<E, A>::Invalid(e1.clone()))
                    }
                },
                (Validated::Invalid(e), _) | (_, Validated::<E, A>::Invalid(e)) => Arc::new(Validated::<E, A>::Invalid(e.clone())),
            }
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Monoid + Clone + Default + PartialEq + 'static> Monoid for Validated<E, A> {
    fn empty(&self) -> AnyBox {
        let default_a = A::default();
        let empty_a = default_a.empty();
        if let Some(empty_val) = empty_a.downcast_ref::<A>() {
            Arc::new(Validated::<E, A>::Valid(empty_val.clone()))
        } else {
            panic!("Failed to downcast to A in empty")
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Clone + Default + PartialEq + 'static> Applicative for Validated<E, A> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(x) => {
                let result = f(x.clone_box());
                if let Some(a) = result.downcast_ref::<A>() {
                    Arc::new(Validated::<E, A>::Valid(a.clone())) as AnyBox
                } else {
                    Arc::new(Validated::<E, A>::Valid(A::default())) as AnyBox
                }
            },
            Validated::Invalid(e) => Arc::new(Validated::<E, A>::Invalid(e.clone())) as AnyBox,
        }
    }

    fn lift2(&self, other: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(other_validated) = other.downcast_ref::<Validated<E, A>>() {
            match (self, other_validated) {
                (Validated::Valid(a1), Validated::Valid(a2)) => {
                    let result = f(Arc::new(a1.clone()) as AnyBox, Arc::new(a2.clone()) as AnyBox);
                    if let Some(value) = result.downcast_ref::<A>() {
                        Arc::new(Validated::<E, A>::Valid(value.clone()))
                    } else {
                        Arc::new(self.clone())
                    }
                },
                (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                    let combined = e1.combine(Arc::new(e2.clone()) as AnyBox);
                    if let Some(e) = combined.downcast_ref::<E>() {
                        Arc::new(Validated::<E, A>::Invalid(e.clone()))
                    } else {
                        Arc::new(Validated::<E, A>::Invalid(e1.clone()))
                    }
                },
                (Validated::Invalid(e), _) | (_, Validated::Invalid(e)) => Arc::new(Validated::<E, A>::Invalid(e.clone())),
            }
        } else {
            Arc::new(self.clone())
        }
    }

    fn lift3(&self, other1: AnyBox, other2: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(other1_validated), Some(other2_validated)) = (
            other1.downcast_ref::<Validated<E, A>>(),
            other2.downcast_ref::<Validated<E, A>>()
        ) {
            match (self, other1_validated, other2_validated) {
                (Validated::Valid(a1), Validated::Valid(a2), Validated::Valid(a3)) => {
                    let result = f(
                        Arc::new(a1.clone()) as AnyBox,
                        Arc::new(a2.clone()) as AnyBox,
                        Arc::new(a3.clone()) as AnyBox,
                    );
                    if let Some(value) = result.downcast_ref::<A>() {
                        Arc::new(Validated::<E, A>::Valid(value.clone()))
                    } else {
                        Arc::new(self.clone())
                    }
                },
                (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                    let temp = e1.combine(Arc::new(e2.clone()) as AnyBox);
                    let combined = if let Some(e) = temp.downcast_ref::<E>() {
                        e.combine(Arc::new(e3.clone()) as AnyBox)
                    } else {
                        Arc::new(e1.clone()) as AnyBox
                    };
                    if let Some(e) = combined.downcast_ref::<E>() {
                        Arc::new(Validated::<E, A>::Invalid(e.clone()))
                    } else {
                        Arc::new(Validated::<E, A>::Invalid(e1.clone()))
                    }
                },
                (Validated::Invalid(e), _, _) | (_, Validated::Invalid(e), _) | (_, _, Validated::Invalid(e)) => {
                    Arc::new(Validated::<E, A>::Invalid(e.clone()))
                }
            }
        } else {
            Arc::new(self.clone())
        }
    }
}

impl<E: ValidatedTypeOps, A: TypeOps + Monoid + Clone + Default + PartialEq + 'static> Monad for Validated<E, A> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Validated::Valid(a) => {
                let result = f(a.clone_box());
                if let Some(validated) = result.downcast_ref::<Self>() {
                    Arc::new(validated.clone())
                } else if let Some(value) = result.downcast_ref::<A>() {
                    Arc::new(Validated::<E, A>::Valid(value.clone()))
                } else {
                    Arc::new(self.clone())
                }
            },
            Validated::Invalid(e) => Arc::new(Validated::<E, A>::Invalid(e.clone())),
        }
    }

    fn join(&self) -> AnyBox {
        match self {
            Validated::Valid(a) => {
                if let Some(inner) = a.clone_box().downcast_ref::<Self>() {
                    Arc::new(inner.clone())
                } else {
                    Arc::new(Validated::<E, A>::Valid(a.clone()))
                }
            },
            Validated::Invalid(e) => Arc::new(Validated::<E, A>::Invalid(e.clone())),
        }
    }
}