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
| `Validated::recover_all` | Deprecated | `recover_all_at_once`, `recover_with` |
| `ContextError::context` | Deprecated | `ContextError::to_contexts` |
| `ContextError::contexts_raw` | Deprecated | `ContextError::contexts` |
| `ContextError::Display` | Changed | Formats context chain only; root error via `source()` |
| `Prism::then` | Changed | Requires `Clone` bounds on closures; returns `+ Clone` |
| `Validated::sequence` | Changed | Accepts generic `IntoIterator<Item = Self>` |

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

---

## 4. `ContextError` Alignment

### Getter Naming

To align with Rust API naming guidelines, accessors now distinguish borrowed from cloned data:

- `err.contexts()` returns `&[String]` (zero-allocation view; replaces `contexts_raw()`).
- `err.to_contexts()` returns `Vec<String>` (cloned vector; replaces `context()`).

`err.context()` and `err.contexts_raw()` remain as deprecated shims for 0.20.0.

### `Display` Formatting

`Display` now formats only the accumulated context chain (`ctx1 -> ctx2`), delegating root error presentation to `Error::source()`. Standard error reporters (`anyhow`, `eyre`) traversing `source()` no longer print the root error twice.

When no context entries exist, `Display` falls back to the root error so output is never empty.

---

## 5. `Prism::then` Closure `Clone` Bounds

`Prism::then` now requires `Clone` on input preview/review closures and returns `+ Clone` closures, matching `Lens::then`:

```rust
// Helper functions creating Prisms used with `.then()` must declare `+ Clone`:
fn my_prism() -> Prism<S, A, impl Fn(&S) -> Option<A> + Clone, impl Fn(A) -> S + Clone> {
    Prism::new(|s| ..., |a| ...)
}
```

This guarantees that composed prisms can be cloned via `Prism::clone`.

---

## 6. `Validated` Changes

### `recover_all` Deprecation

`Validated::recover_all` is deprecated because short-circuiting on the first recovered error silently discards other unrecovered errors in an applicative error collection.

Migrate to `recover_all_at_once` (to inspect all errors together) or `recover_with` (for fallback values):

```rust
// Before (0.19.0)
let recovered = invalid.recover_all(|e| match e { ... });

// After (0.20.0): batch recovery
let recovered = invalid.recover_all_at_once(|errs| {
    if errs.iter().all(|e| is_recoverable(e)) {
        Validated::valid(default_val)
    } else {
        Validated::invalid_many(errs)
    }
});

// Or simple fallback:
let recovered = invalid.recover_with(default_val);
```

### `sequence` Input Relaxation

`Validated::sequence` now accepts any `IntoIterator<Item = Validated<T, E>>` instead of requiring an allocated `Vec`. Existing call sites passing `Vec` continue to compile without change.
