# Error Types Migration Guide

## Overview

Version 0.11.0 introduces structured error types for `Choice`, `Either`, and `Validated` datatypes, replacing `&'static str` error messages with proper enum types.

---

## New Error Types

### Location

All error types are in `rustica::datatypes::error`:

```rust
use rustica::datatypes::error::{ChoiceError, EitherError, ValidatedError};
```

---

## ChoiceError

```rust
pub enum ChoiceError {
    /// No alternatives available for the operation
    NoAlternatives,
    
    /// Index out of bounds for alternatives
    IndexOutOfBounds { index: usize, len: usize },
    
    /// Primary value iterator was empty during flatten
    EmptyPrimaryIterator,
    
    /// Choice is empty (no primary value)
    EmptyChoice,
}
```

### Affected Methods

| Method | Old Return Type | New Return Type |
|--------|-----------------|-----------------|
| `try_first()` | N/A (new) | `Result<&T, ChoiceError>` |
| `try_remove_alternative(i)` | `Result<Self, &'static str>` | `Result<Self, ChoiceError>` |
| `try_flatten()` | `Result<Choice<I>, &'static str>` | `Result<Choice<I>, ChoiceError>` |
| `try_swap_with_alternative(i)` | `Result<Self, &'static str>` | `Result<Self, ChoiceError>` |

### Migration Example

```rust
// OLD (v0.10.x)
match choice.try_flatten() {
    Ok(flat) => { /* ... */ },
    Err(msg) => println!("{}", msg),  // &'static str
}

// NEW (v0.11.0)
use rustica::datatypes::error::ChoiceError;
match choice.try_flatten() {
    Ok(flat) => { /* ... */ },
    Err(ChoiceError::EmptyPrimaryIterator) => {
        println!("Primary value was empty");
    },
    Err(e) => println!("{}", e),  // Display impl
}
```

---

## EitherError

```rust
pub enum EitherError {
    /// Expected Left variant but found Right
    ExpectedLeft,
    
    /// Expected Right variant but found Left
    ExpectedRight,
}
```

### Either Safe Methods

| Method | Return Type | Safe Alternative To |
|--------|-------------|---------------------|
| `try_unwrap_left()` | `Result<L, EitherError>` | `unwrap_left()` |
| `try_unwrap_right()` | `Result<R, EitherError>` | `unwrap_right()` |
| `try_left_ref()` | `Result<&L, EitherError>` | `left_ref()` |
| `try_right_ref()` | `Result<&R, EitherError>` | `right_ref()` |

### Either Usage Example

```rust
use rustica::datatypes::either::Either;
use rustica::datatypes::error::EitherError;

let either: Either<i32, &str> = Either::Right("hello");

// Safe extraction
match either.try_unwrap_left() {
    Ok(left) => println!("Left: {}", left),
    Err(EitherError::ExpectedLeft) => println!("Was Right variant"),
}

// Or use with ? operator
fn get_left(e: Either<i32, &str>) -> Result<i32, EitherError> {
    e.try_unwrap_left()
}
```

---

## ValidatedError

```rust
pub enum ValidatedError {
    /// Expected Valid variant but found Invalid
    ExpectedValid,
    
    /// Expected Invalid variant but found Valid
    ExpectedInvalid,
}
```

### Validated Safe Methods

| Method | Return Type | Safe Alternative To |
|--------|-------------|---------------------|
| `try_unwrap()` | `Result<A, ValidatedError>` | `unwrap_owned()` |
| `try_unwrap_invalid()` | `Result<SmallVec<[E; 8]>, ValidatedError>` | `unwrap_invalid_owned()` |
| `try_valid_ref()` | `Result<&A, ValidatedError>` | Pattern matching |

### Validated Usage Example

```rust
use rustica::datatypes::validated::Validated;
use rustica::datatypes::error::ValidatedError;

let validated: Validated<&str, i32> = Validated::Valid(42);

// Safe extraction
match validated.try_unwrap() {
    Ok(value) => println!("Valid: {}", value),
    Err(ValidatedError::ExpectedValid) => println!("Was Invalid"),
}

// With ? operator in validation pipelines
fn process(v: Validated<&str, i32>) -> Result<i32, ValidatedError> {
    v.try_unwrap()
}
```

---

## Benefits

1. **Type Safety**: Compiler enforces exhaustive error handling
2. **Rich Context**: `IndexOutOfBounds` includes actual index and length
3. **Composability**: Works with `?` operator and `Result` combinators
4. **Display/Error Traits**: All error types implement `Display` and `std::error::Error`

---

## Backward Compatibility

- Original panicking methods (`unwrap_left()`, `unwrap_right()`, etc.) are preserved
- New `try_*` methods are additions, not replacements
- Existing code continues to work unchanged
