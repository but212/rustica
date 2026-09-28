# Rustica 0.20.0 Migration Guide

Removals, breaking changes, and direct replacement patterns for Rustica 0.20.0.

---

## Quick Reference

| Item | Status | Replacement |
| --- | --- | --- |
| `Semigroup for HashMap<K, V>` | Removed | `BTreeMap<K, V>` (`alloc`), or downstream newtype wrapper |
| `Semigroup for HashSet<T>` | Removed | `BTreeSet<T>` (`alloc`), or downstream newtype wrapper |
| Platform support | Changed | Unconditional `#![no_std]` + `alloc`. No feature flag required |
| `fmap` (`Choice`, `Validated`, `Free`, `Program`, `TryProgram`) | Removed | `map` |
| `Lens::fmap` | Removed | `Lens::iso_map` |
| `bind`, `flat_map` (`Free`, `Program`, `TryProgram`) | Removed | `and_then` |
| `Choice::try_flatten_cloned`, `flatten_cloned` | Removed | `.clone().try_flatten()`, `.clone().flatten()` |
| `Validated::to_option` | Removed | `as_option().cloned()` |
| `async` feature, `Validated::*_async` | Removed | Native `match` / `async`/`await` |
| `tokio` dev-dependency | Removed | Native test runners |

---

## 1. `no_std` Migration

Rustica is unconditionally `#![no_std]`, backed by `extern crate alloc`.

No `std` feature flag exists or is needed. Both `std` and `no_std` environments consume Rustica without configuration:

```toml
[dependencies]
rustica = "0.20.0"
```

---

## 2. `HashMap` and `HashSet` `Semigroup` Removal

To eliminate `std` dependencies without external hash-map crates, `Semigroup` for `HashMap` and `HashSet` is removed.

### Option A: `BTreeMap` / `BTreeSet` (Recommended)

`BTreeMap` and `BTreeSet` live in `alloc` and retain full `Semigroup` / `Monoid` implementations.

```rust
// Before (0.19.0)
use std::collections::HashMap;
use rustica::traits::semigroup::Semigroup;

let a = HashMap::from([("k", "v1".to_string())]);
let b = HashMap::from([("k", "v2".to_string())]);
let combined = a.combine(b);

// After (0.20.0)
use alloc::collections::BTreeMap;
use rustica::traits::semigroup::Semigroup;

let a = BTreeMap::from([("k", "v1".to_string())]);
let b = BTreeMap::from([("k", "v2".to_string())]);
let combined = a.combine(b);
```

### Option B: Downstream Newtype Wrapper

For applications requiring `HashMap`:

```rust
use std::collections::HashMap;
use std::hash::Hash;
use rustica::traits::semigroup::Semigroup;

pub struct MapWrapper<K, V>(pub HashMap<K, V>);

impl<K: Eq + Hash, V: Semigroup> Semigroup for MapWrapper<K, V> {
    fn combine(mut self, other: Self) -> Self {
        for (k, v) in other.0 {
            match self.0.remove(&k) {
                Some(existing) => { self.0.insert(k, existing.combine(v)); }
                None => { self.0.insert(k, v); }
            }
        }
        self
    }
}
```

---

## 3. Deprecated Functional Aliases & Async Combinators

Aliases deprecated in 0.19.0 are removed in favor of standard Rust conventions.

### Monadic & Functor Methods

| Removed | Replacement |
| --- | --- |
| `Choice::fmap(f)` | `Choice::map(f)` |
| `Validated::fmap(f)` | `Validated::map(f)` |
| `Free::fmap(f)` | `Free::map(f)` |
| `Program::fmap(f)` | `Program::map(f)` |
| `TryProgram::fmap(f)` | `TryProgram::map(f)` |
| `Lens::fmap(f, g)` | `Lens::iso_map(f, g)` |
| `Free::bind(f)`, `flat_map(f)` | `Free::and_then(f)` |
| `Program::bind(f)` | `Program::and_then(f)` |
| `TryProgram::bind(f)` | `TryProgram::and_then(f)` |

### Collection & Option Helpers

| Removed | Replacement |
| --- | --- |
| `Choice::flatten_cloned()` | `choice.clone().flatten()` |
| `Choice::try_flatten_cloned()` | `choice.clone().try_flatten()` |
| `Validated::to_option()` | `validated.as_option().cloned()` |

### Async Combinators

Replace `Validated::{map_async, map_err_async, and_then_async}` with standard pattern matching and `async`/`await`:

```rust
// Before (0.19.0)
let res = validated.map_async(|x| async move { fetch(x).await }).await;

// After (0.20.0)
let res = match validated {
    Validated::Valid(x) => Validated::Valid(fetch(x).await),
    Validated::Invalid(errs) => Validated::Invalid(errs),
};
```
