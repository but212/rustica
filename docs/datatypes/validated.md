# Validated Datatype (`Validated<T, E>`)

The `Validated` datatype represents a validation result that can either be valid with a value
or invalid with a collection of errors. Unlike `Result`, which fails fast on the first error,
`Validated` can accumulate multiple errors during validation.

## Quick Start

Accumulate validation errors instead of failing fast:

```rust
use rustica::datatypes::validated::Validated;

// Create validation functions
let validate_positive = |x: &i32| -> Validated<i32, String> {
    if *x > 0 {
        Validated::Valid(*x)
    } else {
        Validated::invalid("Must be positive".to_string())
    }
};

let validate_even = |x: &i32| -> Validated<i32, String> {
    if *x % 2 == 0 {
        Validated::Valid(*x)
    } else {
        Validated::invalid("Must be even".to_string())
    }
};

// Combine validations - accumulates ALL errors
let combine_validations = |a: &i32, b: &i32| -> Validated<i32, String> {
    Validated::<i32, String>::lift2(
        |x: i32, y: i32| x + y,
        validate_positive(a),
        validate_even(b)
    )
};

// Success case
let success = combine_validations(&5, &4);
assert_eq!(success, Validated::Valid(9));

// Error accumulation - gets BOTH errors
let errors = combine_validations(&-1, &3);
assert!(errors.is_invalid());
assert_eq!(errors.error_slice().len(), 2);
```

## Trait Implementations

`Validated<T, E>` implements algebraic traits and provides inherent functional methods:

- **Semigroup**: Combines inner values when both are valid via `T::combine`, or concatenates error collections when invalid

Inherent methods like [`bimap`](Validated::bimap), [`map`](Validated::map), [`map_err`](Validated::map_err),
[`zip`](Validated::zip), and [`zip_with`](Validated::zip_with) provide dual-track mappings and applicative combinations without trait bounds.

## Examples

The quick-start example above demonstrates the core workflow. Individual methods document
their minimal invocation; algebraic laws and boundary cases are covered by the unit tests.

## Functional Programming Context

In functional programming, validation is often handled through types that can represent
either success or failure. The `Validated` type is inspired by similar constructs in other
functional programming languages, such as:

- `Validated` in Cats (Scala)
- `Validation` in Arrow (Kotlin)
- `Validation` in fp-ts (TypeScript)

The key difference between `Validated` and `Result` is that `Validated` is designed for
scenarios where you want to collect all validation errors rather than stopping at the first one.

## Type Class Laws

The type-class implementations obey their documented laws; executable law and boundary
checks live in the unit-test module below rather than in independent doctest crates.

## Use Cases

The `Validated` datatype is particularly useful for:

- **Form validation**: Collecting all validation errors at once
- **Configuration validation**: Validating multiple configuration parameters
- **Data parsing**: Accumulating parsing errors from different parts of a document
- **API request validation**: Returning all validation errors to the client

## Function-Level Documentation

For detailed examples of how to use the `Validated` datatype, including:

- Creating valid and invalid instances
- Working with validation results
- Accumulating errors
- Transforming valid and invalid values
- Converting between `Validated` and other types
- Using applicative validation for form validation

Please refer to the documentation of individual functions in this module.
