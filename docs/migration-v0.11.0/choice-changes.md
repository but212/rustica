# Choice Migration Guide

## Overview

Version 0.11.0 makes several changes to `Choice<T>` to focus on its categorical purpose as a nondeterministic computation type.

**Complete Working Example**: See `examples/choice_migration_v0_11_0.rs`

---

## Breaking Changes Summary

1. **MonadPlus Removed** - Use `Alternative` instead
2. **Foldable Clone Bound Removed** - More flexible type constraints
3. **17 Utility Methods Deprecated** - Will be removed in v0.12.0

---

## MonadPlus Removal

### What Changed

```rust
// REMOVED in v0.11.0
impl<T: Clone> MonadPlus for Choice<T> {
    fn mzero<U>() -> Self::Output<U> { ... }
    fn mplus(&self, other: &Self) -> Self { ... }
}
```

### Why

`MonadPlus` was a complete duplicate of `Alternative`:

- `mzero()` ≡ `empty_alt()`
- `mplus()` ≡ `alt()`

### Migration

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

---

## Foldable Clone Bound Removal

```rust
// OLD (v0.10.x)
impl<T: Clone> Foldable for Choice<T> { ... }

// NEW (v0.11.0)
impl<T> Foldable for Choice<T> { ... }
```

`Foldable` only reads values by reference, so `Clone` is unnecessary.

---

## Deprecated Methods (17 total)

These methods are deprecated and will be removed in v0.12.0:

### Convenience Methods

| Deprecated | Replacement |
|------------|-------------|
| `has_alternatives()` | `!alternatives().is_empty()` |
| `to_vec()` | `iter().cloned().collect()` |
| `find_first(pred)` | `iter().find(pred)` |
| `iter_alternatives()` | `alternatives().iter()` |

### Non-Categorical Operations

| Deprecated | Replacement |
|------------|-------------|
| `dedup()` | External `HashSet` pattern |
| `dedup_by_key()` | External `HashMap` pattern |
| `fold(init, f)` | `Foldable::fold_left(init, f)` |
| `to_map_with_key()` | `iter().map().collect()` |
| `add_alternatives()` | `Semigroup::combine()` |
| `remove_alternative(i)` | `filter_values()` |
| `swap_with_alternative(i)` | Explicit reconstruction |

### Semantically Confusing

| Deprecated | Replacement |
|------------|-------------|
| `filter(pred)` | `filter_values(pred)` |
| `fmap_alternatives(f)` | `fmap()` with conditions |
| `flatten_sorted()` | `flatten()` + external sort |
| `bind_lazy(f)` | `bind()` + external iteration |

---

## Migration Examples

### Convenience Methods

```rust
// BEFORE
if choice.has_alternatives() { ... }
let vec = choice.to_vec();
let found = choice.find_first(|&x| x > 2);

// AFTER
if !choice.alternatives().is_empty() { ... }
let vec: Vec<_> = choice.iter().cloned().collect();
let found = choice.iter().find(|&&x| x > 2);
```

### Collection Operations

```rust
// BEFORE
let unique = choice.dedup();
let sum = choice.fold(0, |acc, &x| acc + x);

// AFTER
use std::collections::HashSet;
let unique: Choice<i32> = {
    let mut seen = HashSet::new();
    choice.iter().filter(|&x| seen.insert(*x)).cloned().collect()
};

use rustica::traits::foldable::Foldable;
let sum = choice.fold_left(0, |acc, &x| acc + x);
```

### Combining Choices

```rust
// BEFORE
let expanded = choice.add_alternatives(vec![5, 6]);

// AFTER
use rustica::traits::semigroup::Semigroup;
let expanded = choice.combine(&Choice::new(5, vec![6]));
```

---

## Retained Core Operations

```rust
// Creation
Choice::new(primary, alternatives)
Choice::new_empty()
Choice::of_many(iter)

// Access
choice.first()
choice.alternatives()
choice.len()
choice.is_empty()
choice.iter()

// Categorical
choice.filter_values(pred)  // Clear semantics
choice.flatten()            // Monadic
choice.try_flatten()        // Safe variant
choice.fmap(f)              // Functor
choice.apply(other)         // Applicative
choice.bind(f)              // Monad
choice.combine(other)       // Semigroup
choice.alt(other)           // Alternative
```

---

## Timeline

- **v0.11.0**: Utility methods deprecated
- **v0.12.0**: Deprecated methods removed

---

## Run the Example

```bash
cargo run --example choice_migration_v0_11_0
```
