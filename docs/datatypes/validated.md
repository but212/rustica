# Validated (`Validated<T, E>`)

Accumulates errors during validation, unlike `Result` which fails fast on the first error.

## Quick Start

```rust
use rustica::datatypes::validated::Validated;

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

let combine_validations = |a: &i32, b: &i32| -> Validated<i32, String> {
    Validated::<i32, String>::lift2(
        |x: i32, y: i32| x + y,
        validate_positive(a),
        validate_even(b),
    )
};

// Success
let success = combine_validations(&5, &4);
assert_eq!(success, Validated::Valid(9));

// Accumulates both errors
let errors = combine_validations(&-1, &3);
assert!(errors.is_invalid());
assert_eq!(errors.error_slice().len(), 2);
```

## Trait Implementations

- **[`Semigroup`](crate::traits::semigroup::Semigroup)**: Combines inner values via `T::combine` when both are valid; concatenates error collections when invalid.

Inherent methods like [`bimap`](Validated::bimap), [`map`](Validated::map), [`map_err`](Validated::map_err), [`zip`](Validated::zip), and [`zip_with`](Validated::zip_with) provide dual-track mappings and applicative combinations without trait bounds.

## Use Cases

- **Form validation**: Collects all invalid field errors at once.
- **Configuration validation**: Reports all invalid parameter settings.
- **Data parsing / API requests**: Returns all validation failures in a single response.
