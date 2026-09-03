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

#[cfg(test)]
mod unit_tests {
    use super::{collect_errors, split_validated_errors};
    use crate::datatypes::validated::Validated;

    #[test]
    fn owned_error_conversions_preserve_values() {
        struct NoClone(&'static str);
        let collected = collect_errors([NoClone("error")]);
        assert_eq!(collected.error_slice()[0].0, "error");
        let split = split_validated_errors(Validated::<NoClone, ()>::invalid(NoClone("split")));
        let mut split = split.into_iter();
        assert!(matches!(split.next(), Some(Err(NoClone("split")))));
        assert!(split.next().is_none());
    }
}
