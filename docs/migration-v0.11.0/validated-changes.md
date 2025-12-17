# Validated Typeclass Cleanup Guide

## Overview

Version 0.11.0 removes several typeclass implementations from `Validated<E, A>` that were either mathematically incorrect or semantically confusing.

---

## Breaking Changes

### 1. Monoid Implementation Removed

```rust
// REMOVED - no lawful identity element exists
impl<E, A> Monoid for Validated<E, A> { ... }
```

**Why**: Error-accumulating validation has no meaningful identity element. What would `mempty` return - `Valid` with what value?

**Migration**:

```rust
// OLD
use rustica::traits::monoid::Monoid;
let empty: Validated<String, i32> = Monoid::mempty();

// NEW - use domain-specific neutral values
let empty = Validated::valid(default_value);

// Or model error collections separately
let errors: Vec<String> = vec![];
```

### 2. AsRef Implementation Removed

```rust
// REMOVED - violated AsRef's total conversion contract
impl<E, A> AsRef<A> for Validated<E, A> { ... }
```

**Why**: The previous implementation panicked on `Invalid`, but `AsRef` should be a total function (always succeed).

**Migration**:

```rust
// OLD (panicked on Invalid!)
let validated: Validated<String, i32> = Validated::invalid("error".into());
let ref_val: &i32 = validated.as_ref(); // 💥 panic!

// NEW - use safe methods
let validated: Validated<String, i32> = Validated::valid(42);

// Option 1: Pattern matching
match &validated {
    Validated::Valid(a) => println!("Value: {}", a),
    Validated::Invalid(_) => println!("Has errors"),
}

// Option 2: Safe accessor (returns Option)
if let Some(value) = validated.as_ref() {
    println!("Value: {}", value);
}
```

### 3. MonadPlus and Alternative Removed

```rust
// REMOVED - avoid mixing fail-fast and error accumulation
impl<E, A> MonadPlus for Validated<E, A> { ... }
impl<E, A> Alternative for Validated<E, A> { ... }
```

**Why**: `MonadPlus`/`Alternative` imply fail-fast choice semantics, which conflicts with `Validated`'s purpose of accumulating all errors.

**Migration**:

```rust
// OLD
use rustica::traits::alternative::Alternative;
let result = validated1.alt(&validated2);

// NEW - use recommended helpers
use rustica::datatypes::validated::Validated;

// Recover from all errors
let result = Validated::recover_all(vec![validated1, validated2]);

// Or sequence with error accumulation
let result = Validated::sequence_owned(vec![validated1, validated2]);
```

---

## Recommended Patterns

### Error Accumulation

```rust
use rustica::datatypes::validated::Validated;

fn validate_user(name: &str, age: i32) -> Validated<Vec<String>, User> {
    let name_result = if name.is_empty() {
        Validated::invalid(vec!["Name cannot be empty".to_string()])
    } else {
        Validated::valid(name.to_string())
    };

    let age_result = if age < 0 {
        Validated::invalid(vec!["Age must be non-negative".to_string()])
    } else {
        Validated::valid(age)
    };

    // Combine with applicative - accumulates ALL errors
    name_result.zip_with(&age_result, |n, a| User { name: n, age: a })
}
```

### Recovery Patterns

```rust
// Try multiple validations, collect all that succeed
let results = Validated::recover_all(validations);

// Try multiple, return first success or all errors
let result = Validated::recover_all_at_once(validations);

// Sequence all validations, accumulating errors
let all_valid = Validated::sequence_owned(validations);
```

---

## Summary

| Removed | Reason | Migration |
|---------|--------|-----------|
| `Monoid` | No lawful identity | Use `Validated::valid(default)` |
| `AsRef<A>` | Panicked on Invalid | Use pattern matching or safe accessors |
| `MonadPlus` | Conflicts with error accumulation | Use `recover_all` |
| `Alternative` | Conflicts with error accumulation | Use `recover_all_at_once` |

The remaining `Validated` API focuses purely on error-accumulating validation with clear Applicative semantics.
