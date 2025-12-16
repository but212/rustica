# Choice Migration Guide v0.11.0

This document outlines the breaking changes and improvements to `Choice` in v0.11.0.

## Removed MonadPlus Implementation

### Removed MonadPlus: What Changed

The `MonadPlus` trait implementation has been removed from `Choice<T>`.

```rust
// REMOVED in v0.11.0
impl<T: Clone> MonadPlus for Choice<T> {
    fn mzero<U>() -> Self::Output<U> { ... }
    fn mplus(&self, other: &Self) -> Self { ... }
    fn mplus_owned(self, other: Self) -> Self { ... }
}
```

### Removed MonadPlus: Why

`MonadPlus` was a complete duplicate of `Alternative` for `Choice<T>`:

- `mzero()` was identical to `empty_alt()`
- `mplus()` was identical to `alt()`
- `mplus_owned()` was identical to `alt_owned()`

This redundancy created confusion without adding value.

### Removed MonadPlus: Migration Path

Replace `MonadPlus` usage with `Alternative`:

```rust
// OLD (v0.10.x)
use rustica::traits::monad_plus::MonadPlus;
let empty: Choice<i32> = <Choice<i32> as MonadPlus>::mzero();
let combined = a.mplus(&b);

// NEW (v0.11.0)
use rustica::traits::alternative::Alternative;
let empty: Choice<i32> = <Choice<i32> as Alternative>::empty_alt();
let combined = a.alt(&b);
```

## Semigroup Documentation Update

### Semigroup: What Changed

Added documentation to clarify that `Semigroup::combine` and `Alternative::alt` have identical behavior for `Choice<T>`.

### Semigroup: Why

Both operations represent the same concept for non-deterministic computation: collecting all possible alternatives. The documentation now explicitly states this relationship.

## Documentation Changes for flatten()

### flatten(): What Changed

Added a safety note to `flatten()` method documentation to highlight the panic risk and direct users to `try_flatten()`.

### flatten(): Why

Make the API safer by ensuring users are aware of the panic condition and know about the safe alternative.

## Type Constraint Improvements

### Type Constraints: What Changed

Removed unnecessary `Clone` bound from `Foldable` implementation:

```rust
// OLD (v0.10.x)
impl<T: Clone> Foldable for Choice<T> { ... }

// NEW (v0.11.0)
impl<T> Foldable for Choice<T> { ... }
```

### Type Constraints: Why

`Foldable` only reads values by reference, so `Clone` is not required. This reduces type constraints and improves flexibility.

## Test Updates

The test `test_choice_alternative_and_monadplus_traits` has been renamed to `test_choice_alternative_trait` and now only tests `Alternative` methods.

## Summary

- ✅ MonadPlus removed (use Alternative instead)
- ✅ Semigroup::combine vs Alternative::alt relationship documented
- ✅ flatten() safety improved with better documentation
- ✅ Unnecessary Clone bound removed from Foldable
- ✅ Tests updated to reflect changes

These changes make the `Choice<T>` API cleaner, more consistent, and easier to understand while maintaining all core functionality.
