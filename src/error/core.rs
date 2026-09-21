//! # Core Error Category Theory Abstractions
//!
//! This module provides foundational abstractions for composable, type-safe error management.

use crate::datatypes::validated::{NonEmptyErrors, Validated, core::ErrorVec};

pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Validated<E, Vec<B>>
where
    F: FnMut(A) -> Result<B, E>,
{
    let mut values = Vec::new();
    let mut errors = ErrorVec::new();

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => errors.push(error),
        }
    }

    match NonEmptyErrors::try_from_vec(errors) {
        Some(errors) => Validated::Invalid(errors),
        None => Validated::Valid(values),
    }
}

#[cfg(test)]
mod tests {
    use super::traverse_validated;
    use crate::datatypes::validated::Validated;

    #[test]
    fn traverse_validated_accumulates_errors_in_input_order() {
        let result = traverse_validated([1, 2, 3], |value| {
            if value % 2 == 0 {
                Ok(value * 10)
            } else {
                Err(format!("odd:{value}"))
            }
        });

        assert_eq!(
            result,
            Validated::invalid_many(["odd:1".to_string(), "odd:3".to_string()])
        );
    }

    #[test]
    fn traverse_validated_keeps_all_successes() {
        let result = traverse_validated([1, 2, 3], |value| Ok::<_, String>(value * 10));

        assert_eq!(result, Validated::valid(vec![10, 20, 30]));
    }
}
