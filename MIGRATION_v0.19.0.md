# Rustica 0.19.0 Migration Guide

This guide details all removals and breaking changes in Rustica 0.19.0, with concrete replacement patterns for each removed type, trait, and function.

---

## Quick Reference Summary

| Removed Item | Direct Replacement |
| --- | --- |
| `pvec::*`, `PersistentVector<T>`, `pvec!` macro | `imbl::Vector` or standard `std::vec::Vec<T>` |
| `pvec` Cargo feature | Remove from `Cargo.toml`; `full` feature bundle no longer includes it |
| `traits::HKT` | Native generic types and inherent methods |
| `traits::Functor` / `fmap` | Inherent `map` (or inherent `fmap` alias preserved on `Choice` and `Validated`), or `Iterator::map` |
| `traits::Pure` / `pure` | Concrete constructors (`Validated::valid`, `Choice::single`, `Some`, `Ok`) |
| `traits::Applicative` / `apply`, `lift2`, `lift3` | Inherent `Validated::apply`, `zip_with`, `zip`, `lift2`, `lift3` |
| `traits::Foldable` / `fold_left`, `fold_right` | Standard `Iterator::fold`, `Iterator::rfold` |
| `traits::Monad` / `bind`, `join` | Inherent `and_then`, native `?` operator, or `Iterator::flat_map` |
| `Prism::set_if_different` | Inherent `Prism::set` ($O(1)$ unconditional move reconstruction) |
| `datatypes::validated::{combinators, traits}` | Internalized; import from `datatypes::validated::*` or `...::core::*` |

---

## 1. Persistent Collections (`pvec`)

The entire `rustica::pvec` module, `PersistentVector<T>`, and the `pvec!` macro have been removed.

### Migration Path

Users requiring persistent collections with structural sharing should migrate to dedicated persistent data structure crates such as [`imbl`](https://crates.io/crates/imbl) (`imbl::Vector`), or standard `std::vec::Vec<T>`:

```rust
// Before (0.18.0)
use rustica::pvec::PersistentVector;
let vec: PersistentVector<i32> = (0..100).collect();
let updated = vec.push_back(100);

// After (0.19.0) with imbl
use imbl::Vector;
let mut vec: Vector<i32> = (0..100).collect();
vec.push_back(100);

// Or with standard Vec
let mut vec: Vec<i32> = (0..100).collect();
vec.push(100);
```

### Feature Flag Cleanup

The `pvec` Cargo feature flag has been removed. In `Cargo.toml`:

```toml
# Before (0.18.0)
rustica = { version = "0.18.0", features = ["pvec"] }

# After (0.19.0)
rustica = "0.19.0"
```

The `full` feature bundle now expands to `["async", "serde", "quickcheck"]`.

---

## 2. Categorical Simulation Traits

The simulated higher-kinded type and category theory traits (`HKT`, `Functor`, `Pure`, `Applicative`, `Monad`, and `Foldable`) have been removed in favor of native Rust idioms and inherent methods on concrete types.

The core algebraic traits **`Semigroup`** and **`Monoid`** are fully preserved.

### Mapping (`Functor::fmap` → `map`)

```rust
// Before (0.18.0)
use rustica::traits::functor::Functor;
let v = Validated::<i32, &str>::valid(10).fmap(|x| x * 2);
let c = Choice::single(10).fmap(|x| x * 2);

// After (0.19.0)
let v = Validated::<i32, &str>::valid(10).map(|x| x * 2);
let c = Choice::single(10).map(|x| x * 2);
// Inherent `fmap` alias is also preserved directly on `Choice` and `Validated`:
let v = Validated::<i32, &str>::valid(10).fmap(|x| x * 2);
let c = Choice::single(10).fmap(|x| x * 2);
// Or on standard Option/Result/Iterator:
let opt = Some(10).map(|x| x * 2);
```

### Context Construction (`Pure::pure` → Concrete Constructors)

```rust
// Before (0.18.0)
use rustica::traits::pure::Pure;
let v: Validated<i32, &str> = <Validated<i32, &str> as Pure>::pure(42);

// After (0.19.0)
let v: Validated<i32, &str> = Validated::valid(42);
let c: Choice<i32> = Choice::single(42);
let opt: Option<i32> = Some(42);
let res: Result<i32, ()> = Ok(42);
```

### Applicative Combination (`Applicative::apply` / `lift2` → `zip_with` / `collect`)

```rust
// Before (0.18.0)
use rustica::traits::applicative::Applicative;
let v1: Validated<i32, &str> = Validated::valid(10);
let v2: Validated<i32, &str> = Validated::valid(20);
let sum = Validated::<i32, &str>::lift2(|a, b| a + b, v1, v2);

// After (0.19.0)
let v1: Validated<i32, &str> = Validated::valid(10);
let v2: Validated<i32, &str> = Validated::valid(20);
let sum = v1.zip_with(v2, |a, b| a + b);

// Inherent `apply` is also preserved directly on `Validated`:
let f: Validated<fn(i32) -> i32, &str> = Validated::valid(|x| x + 10);
let v = Validated::<i32, &str>::valid(20);
let res = f.apply(v);

// For collections:
let items = vec![Validated::<i32, &str>::valid(1), Validated::valid(2)];
let collected: Validated<Vec<i32>, &str> = items.into_iter().collect();
```

### Monadic Binding (`Monad::bind` / `join` → `and_then` / `?`)

```rust
// Before (0.18.0)
use rustica::traits::monad::Monad;
let res: Result<i32, &str> = Ok(5).bind(|n| Ok(n + 1));

// After (0.19.0)
let res: Result<i32, &str> = Ok(5).and_then(|n| Ok(n + 1));
// Or using native `?`:
fn step() -> Result<i32, &'static str> {
    let n = Ok(5)?;
    Ok(n + 1)
}
```

### Folding (`Foldable::fold_left` / `fold_right` → `Iterator::fold` / `rfold`)

```rust
// Before (0.18.0)
use rustica::traits::foldable::Foldable;
let folded = choice.fold_left(0, |acc, &x| acc + x);

// After (0.19.0)
let folded = choice.iter().fold(0, |acc, &x| acc + x);
```

---

## 3. Optics (`Prism::set_if_different`)

`Prism::set_if_different` has been removed. Reconstructing an enum variant via `review` is an $O(1)$ pointer/variant move; equality-checking payloads introduced unnecessary `PartialEq` bounds and redundant cloning.

```rust
// Before (0.18.0)
let updated = prism.set_if_different(status, "Bob".to_string());

// After (0.19.0)
let updated = prism.set(status, "Bob".to_string());
```

---

## 4. Prelude Changes

`rustica::prelude::*` and `rustica::prelude::traits::*` now re-export exclusively the algebraic traits:
- `Semigroup`
- `Monoid`

All concrete types (`Validated`, `Choice`, `Free`, `Lens`, `Prism`, `Program`, `TryProgram`) and error utilities (`ContextError`, `context!`) remain available as before.

---

## 5. Validated Submodule Consolidation

Following the removal of categorical simulation traits, the empty submodules `rustica::datatypes::validated::combinators` and `rustica::datatypes::validated::traits` have been internalized:
- Trait implementations (`Semigroup`, `Arbitrary`) now reside directly within `core.rs`.
- Inherent combinators continue to be methods on `Validated`.
- Canonical imports remain `rustica::datatypes::validated::{Validated, NonEmptyErrors}` and `rustica::prelude::*`.
- `rustica::datatypes::validated::core::*` and `rustica::datatypes::validated::iter::*` remain public modules.

