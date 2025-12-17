use rustica::datatypes::error::{ChoiceError, EitherError, ValidatedError};

#[test]
fn test_choice_error_display() {
    assert_eq!(
        ChoiceError::NoAlternatives.to_string(),
        "Choice operation failed: no alternatives available"
    );

    assert_eq!(
        ChoiceError::index_out_of_bounds(5, 3).to_string(),
        "Choice::remove_alternative(): index 5 out of bounds for 3 alternatives"
    );

    assert_eq!(
        ChoiceError::EmptyPrimaryIterator.to_string(),
        "Choice::flatten(): primary value produced empty iterator"
    );

    assert_eq!(
        ChoiceError::EmptyChoice.to_string(),
        "Choice operation failed: choice is empty"
    );
}

#[test]
fn test_either_error_display() {
    assert_eq!(
        EitherError::ExpectedLeft.to_string(),
        "Either::unwrap_left(): called on Right variant"
    );

    assert_eq!(
        EitherError::ExpectedRight.to_string(),
        "Either::unwrap_right(): called on Left variant"
    );
}

#[test]
fn test_validated_error_display() {
    assert_eq!(
        ValidatedError::ExpectedValid.to_string(),
        "Validated::unwrap(): called on Invalid variant"
    );

    assert_eq!(
        ValidatedError::ExpectedInvalid.to_string(),
        "Validated::unwrap_invalid(): called on Valid variant"
    );
}

#[test]
fn test_choice_error_predicates() {
    assert!(ChoiceError::NoAlternatives.is_no_alternatives());
    assert!(!ChoiceError::NoAlternatives.is_index_out_of_bounds());

    let idx_err = ChoiceError::index_out_of_bounds(1, 2);
    assert!(idx_err.is_index_out_of_bounds());
    assert!(!idx_err.is_no_alternatives());

    assert!(ChoiceError::EmptyPrimaryIterator.is_empty_primary_iterator());
    assert!(ChoiceError::EmptyChoice.is_empty_choice());
}

#[test]
fn test_either_error_predicates() {
    assert!(EitherError::ExpectedLeft.is_expected_left());
    assert!(!EitherError::ExpectedLeft.is_expected_right());

    assert!(EitherError::ExpectedRight.is_expected_right());
    assert!(!EitherError::ExpectedRight.is_expected_left());
}

#[test]
fn test_validated_error_predicates() {
    assert!(ValidatedError::ExpectedValid.is_expected_valid());
    assert!(!ValidatedError::ExpectedValid.is_expected_invalid());

    assert!(ValidatedError::ExpectedInvalid.is_expected_invalid());
    assert!(!ValidatedError::ExpectedInvalid.is_expected_valid());
}
