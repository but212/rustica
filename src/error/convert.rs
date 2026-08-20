//! Conversions that preserve error accumulation semantics.

use crate::datatypes::validated::Validated;

/// Collects zero or more errors into `Validated`.
pub fn collect_errors<E, I>(errors: I) -> Validated<E, ()>
where
    I: IntoIterator<Item = E>,
{
    let errors: Vec<E> = errors.into_iter().collect();
    if errors.is_empty() {
        Validated::Valid(())
    } else {
        Validated::invalid_many(errors)
    }
}

/// Expands accumulated errors into individual fail-fast results.
pub fn split_validated_errors<T, E>(validated: Validated<E, T>) -> Vec<Result<T, E>> {
    match validated {
        Validated::Valid(value) => vec![Ok(value)],
        Validated::Invalid(errors) => errors.into_iter().map(Err).collect(),
    }
}
