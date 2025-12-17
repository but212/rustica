# Identity Trait Removal Guide

## Overview

Version 0.11.0 removes the incorrect `Functor: Identity` dependency and completely removes the `Identity` trait. This aligns Rustica with proper category theory principles and unifies all value extraction to standard `unwrap()` methods.

**Complete Working Example**: See `examples/identity_migration_v0_11_0.rs`

---

## What Changed?

### Before (v0.10.x)

```rust
pub trait Functor: Identity {  // ❌ Wrong dependency
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>;
}
```

### After (v0.11.0)

```rust
pub trait Functor: HKT {  // ✅ Correct - no Identity
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>;
}

// Identity trait completely removed
```

---

## Why This Change?

### Category Theory Violations

1. **Functor ≠ Value Extraction**: Functors map morphisms `fmap: (A → B) → F(A) → F(B)`, they don't need value extraction
2. **Name Confusion**: "Identity" in category theory = Identity functor `Id(A) = A`, not value extraction
3. **Redundant Abstraction**: `value()` just wrapped standard Rust methods

### Inconsistent API → Unified API

```rust
// BEFORE: Multiple different ways
option.value()              // Identity trait
maybe.get_value()           // Custom method
choice.primary_value()      // Custom method

// AFTER: Unified to standard unwrap()
option.unwrap()             // ✅ Standard
maybe.unwrap()              // ✅ Standard
choice.first().expect()     // ✅ Standard pattern
```

---

## Migration Steps

### Step 1: Replace Identity Methods

```rust
// BEFORE (v0.10.x)
use rustica::traits::identity::Identity;

let option = Some(42);
let value = option.value();           // ❌ Removed
let safe = option.try_value();        // ❌ Removed
let owned = option.into_value();      // ❌ Removed

// AFTER (v0.11.0)
let option = Some(42);
let value = option.unwrap();          // ✅ Standard Rust
let safe = option.as_ref();           // ✅ Standard Rust
let owned = option.unwrap();          // ✅ Standard Rust
```

### Step 2: Use Comonad for Total Extraction

```rust
// BEFORE
use rustica::traits::identity::Identity;
let id = Id::new(42);
let value = id.value();               // ❌ Removed

// AFTER
use rustica::traits::comonad::Comonad;
let id = Id::new(42);
let value = id.extract();             // ✅ Comonad (always succeeds)
```

### Step 3: Remove Identity Bounds

```rust
// BEFORE
fn process<F>(functor: F) -> F::Output<String>
where
    F: Functor + Identity,  // ❌ Identity no longer exists
{
    functor.fmap(|x| format!("{:?}", x))
}

// AFTER
fn process<F>(functor: F) -> F::Output<String>
where
    F: Functor,  // ✅ Just Functor
{
    functor.fmap(|x| format!("{:?}", x))
}
```

### Step 4: Update Custom Types

If you implemented `Identity` for your types:

```rust
// BEFORE
impl<T> Identity for MyWrapper<T> {
    fn value(&self) -> &Self::Source { &self.0 }
    fn into_value(self) -> Self::Source { self.0 }
}

// AFTER - Option A: Just remove it (most cases)
// No Identity needed

// AFTER - Option B: Use Comonad (if total extraction needed)
impl<T: Clone> Comonad for MyWrapper<T> {
    fn extract(&self) -> Self::Source { self.0.clone() }
    fn duplicate(&self) -> Self { self.clone() }
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where F: Fn(&Self) -> U {
        MyWrapper(f(self))
    }
}
```

---

## Value Extraction Methods by Type

| Type | Standard Methods | Safe Methods | Comonad |
|------|------------------|--------------|---------|
| `Option<T>` | `unwrap()`, `unwrap_or()` | `as_ref()`, `ok_or()` | N/A |
| `Result<T, E>` | `unwrap()`, `unwrap_or()` | `as_ref()`, `map_err()` | N/A |
| `Maybe<T>` | `unwrap()`, `unwrap_or()` | `as_option()` | N/A |
| `Choice<T>` | `first().expect()` | `first()`, `iter()` | N/A |
| `Either<L, R>` | `unwrap()`, `unwrap_or()` | `right()`, `left()` | N/A |
| `Id<T>` | `unwrap()` | N/A | `extract()` |

---

## Quick Reference

| Old (v0.10.x) | New (v0.11.0) | Reason |
|---------------|---------------|--------|
| `Functor: Identity` | `Functor: HKT` | Category theory correctness |
| `value()` | `unwrap()` | Standard Rust method |
| `try_value()` | `as_ref()` | Standard Rust method |
| `into_value()` | `unwrap()` | Standard Rust method |
| `id.value()` | `id.extract()` | Comonad for total extraction |

---

## Run the Example

```bash
cargo run --example identity_migration_v0_11_0
```
