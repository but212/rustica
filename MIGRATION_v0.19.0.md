# Rustica 0.19.0 Migration Guide

This guide details all removals and breaking changes in Rustica 0.19.0, with concrete replacement patterns for each removed type, trait, and function.

---

## Quick Reference Summary

| Removed Item | Direct Replacement |
| --- | --- |
| `pvec::*`, `PersistentVector<T>`, `pvec!` macro | `imbl::Vector` or standard `std::vec::Vec<T>` |
| `pvec` Cargo feature | Remove from `Cargo.toml`; `full` feature bundle no longer includes it |
| `traits::HKT` | Native generic types and inherent methods |
| `traits::Functor` / `fmap` | Inherent `map` (`fmap` alias deprecated in 0.19.0; removal in 0.20.0), or `Iterator::map` |
| `traits::Pure` / `pure` | Concrete constructors (`Validated::valid`, `Choice::single`, `Some`, `Ok`) |
| `traits::Applicative` / `apply`, `lift2`, `lift3` | Inherent `Validated::apply`, `zip_with`, `zip`, `lift2`, `lift3` |
| `traits::Foldable` / `fold_left`, `fold_right` | Standard `Iterator::fold`, `Iterator::rfold` |
| `traits::Monad` / `bind`, `join` | Inherent `and_then`, native `?` operator, or `Iterator::flat_map` |
| `Prism::set_if_different` | Inherent `Prism::set` ($O(1)$ unconditional move reconstruction) |
| `enum Free<F, A> { Pure, Suspend, Bind }` | Opaque `struct Free<F, A>` with constructors (`Free::pure`, `Free::suspend`) and accessors (`is_*`, `as_*`) |
| `Free::into_any` | Private implementation detail; internal type-erasure is fully encapsulated |
| `ContStack<F>` | Removed (internal trampoline uses `Vec<Frame<F>>`) |
| `datatypes::validated::{combinators, traits}` | Internalized; import from `datatypes::validated::*` or `...::core::*` |
| `async` feature, `Validated::*_async` | Deprecated in 0.19.0 (removal in 0.20.0); native `match` / `async`/`await` |
| `fmap` (`Choice`, `Validated`, `Free`, `Program`, `TryProgram`) | Deprecated in 0.19.0 (removal in 0.20.0); use `map` |
| `Lens::fmap` | Deprecated in 0.19.0 (removal in 0.20.0); use `Lens::iso_map` |
| `bind`, `flat_map` (`Free`, `Program`, `TryProgram`) | Deprecated in 0.19.0 (removal in 0.20.0); use `and_then` |
| `Choice::try_flatten_cloned`, `flatten_cloned` | Deprecated in 0.19.0 (removal in 0.20.0); use `.clone().try_flatten()`, `.clone().flatten()` |

---

## 1. Persistent Collections (`pvec`)

The entire `rustica::pvec` module, `PersistentVector<T>`, and the `pvec!` macro have been removed.

### Migration Path

Migrate persistent collections with structural sharing to dedicated crates such as [`imbl`](https://crates.io/crates/imbl) (`imbl::Vector`) or standard `std::vec::Vec<T>`:

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

The `full` feature bundle now expands to `["async", "serde", "quickcheck"]` (`async` is deprecated and scheduled for removal in 0.20.0).

---

## 2. Categorical Simulation Traits

Simulated higher-kinded type and category traits (`HKT`, `Functor`, `Pure`, `Applicative`, `Monad`, `Foldable`) are removed in favor of native Rust idioms and inherent methods on concrete types.

Core algebraic traits **`Semigroup`** and **`Monoid`** remain fully supported.

### Mapping (`Functor::fmap` → `map`)

```rust
// Before (0.18.0)
use rustica::traits::functor::Functor;
let v = Validated::<i32, &str>::valid(10).fmap(|x| x * 2);
let c = Choice::single(10).fmap(|x| x * 2);

// After (0.19.0)
let v = Validated::<i32, &str>::valid(10).map(|x| x * 2);
let c = Choice::single(10).map(|x| x * 2);
// Note: inherent `fmap` is deprecated in 0.19.0 in favor of standard `map`.
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

## 3. Optics (`Lens` and `Prism`)

`Prism::set_if_different` has been removed. Enum variant reconstruction via `review` is an $O(1)$ variant move; equality checks incurred unnecessary `PartialEq` bounds and redundant cloning.

```rust
// Before (0.18.0)
let updated = prism.set_if_different(status, "Bob".to_string());

// After (0.19.0)
let updated = prism.set(status, "Bob".to_string());
```

### `Lens::modify` Non-`Clone` Focus & `FnOnce` Support

`Lens::modify` requires only `A: PartialEq`, restoring support for non-`Clone` focus types. Transformation closures on `modify` and `modify_always` accept `F: FnOnce(A) -> A`, allowing closures that move captured state.

### `Lens::then` & `Lens::iso_map` `Clone` Bounds

`Lens::then` eliminates `Arc` allocation for getter sharing. Sequential composition requires closure accessors to implement `Clone` (`GetFn: Clone`, `SetFn: Clone`, `GetFn2: Clone`, `SetFn2: Clone`).

`Lens::iso_map` and deprecated `Lens::fmap` similarly require `Clone` on mapping functions and input accessors (`F: Clone`, `G: Clone`, `GetFn: Clone`, `SetFn: Clone`), returning closures with `+ Clone` to allow composition with `then`.

`Lens` implements `Clone` manually without imposing `S: Clone` or `A: Clone` bounds on target types.

---

## 4. Prelude Changes

`rustica::prelude::*` and `rustica::prelude::traits::*` now re-export exclusively the algebraic traits:

- `Semigroup`
- `Monoid`

All concrete types (`Validated`, `Choice`, `Free`, `Lens`, `Prism`, `Program`, `TryProgram`) and error utilities (`ContextError`, `context!`) remain available as before.

---

## 5. Validated Submodule Consolidation

Following categorical trait removal, the empty submodules `rustica::datatypes::validated::combinators` and `rustica::datatypes::validated::traits` have been internalized:

- Trait implementations (`Semigroup`, `Arbitrary`) now reside directly within `core.rs`.
- Inherent combinators continue as methods on `Validated`.
- Canonical imports remain `rustica::datatypes::validated::{Validated, NonEmptyErrors}` and `rustica::prelude::*`.
- `rustica::datatypes::validated::core::*` and `rustica::datatypes::validated::iter::*` remain public modules.

---

## 6. Deprecations (Scheduled for Removal in 0.20.0)

### `async` Feature Flag & `Validated` Async Combinators

The `async` Cargo feature flag and three async combinators on `Validated` (`map_async`, `map_err_async`, and `and_then_async`) are deprecated in 0.19.0 and scheduled for removal in 0.20.0.

Per Rustica's design rationale ([docs/DESIGN_RATIONALE.md](docs/DESIGN_RATIONALE.md)), native Rust control flow (`async`/`await` and pattern matching) replaces specialized async combinators. Because `Validated` async combinators rely purely on `std::future::Future` without an external runtime, the dedicated feature flag is redundant.

#### Migration to Native Async Control Flow

Replace `Validated` async combinators with native `match` expressions or standard control flow:

```rust
// Before (0.18.0 / 0.19.0 deprecated)
let mapped = validated.map_async(|x| async move { fetch_data(x).await }).await;

// After (Native async/await pattern matching)
let mapped = match validated {
    Validated::Valid(x) => Validated::Valid(fetch_data(x).await),
    Validated::Invalid(errs) => Validated::Invalid(errs),
};

// Before (0.18.0 / 0.19.0 deprecated)
let chained = validated.and_then_async(|x| async move { validate_remote(x).await }).await;

// After (Native async/await pattern matching)
let chained = match validated {
    Validated::Valid(x) => validate_remote(x).await,
    Validated::Invalid(errs) => Validated::Invalid(errs),
};

// Before (0.18.0 / 0.19.0 deprecated)
let mapped_err = invalid.map_err_async(|e| async move { format_err_async(e).await }).await;

// After (Sequential async iteration)
let mapped_err = match invalid {
    Validated::Valid(x) => Validated::Valid(x),
    Validated::Invalid(errs) => {
        let mut results = Vec::with_capacity(errs.len());
        for err in errs {
            results.push(format_err_async(err).await);
        }
        Validated::invalid_many(results)
    },
};
```

### `tokio` Dev-Dependency

`tokio` in `[dev-dependencies]` is deprecated in 0.19.0 (retained exclusively to run unit tests for deprecated `Validated` async combinators) and scheduled for removal in 0.20.0 alongside those tests.

### Datatypes Redundant Aliases & Cloned Forwarders

In 0.19.0, redundant functional aliases (`fmap`, `bind`, `flat_map`) and implicit clone forwarders (`flatten_cloned`, `try_flatten_cloned`) are deprecated and scheduled for removal in 0.20.0 to align Rustica with standard Rust naming conventions (`map`, `and_then`). Optics are the exception: `Lens::fmap` migrates to `Lens::iso_map`, because `Lens` is not a functor and the transformation must be an isomorphism to preserve the lens laws.

| Type | Deprecated Method | Direct Replacement |
| --- | --- | --- |
| `Choice<T>` | `fmap(f)` | `map(f)` |
| `Choice<T>` | `try_flatten_cloned()` | `.clone().try_flatten()` |
| `Choice<T>` | `flatten_cloned()` | `.clone().flatten()` |
| `Validated<T, E>` | `fmap(f)` | `map(f)` |
| `Lens<S, A, ...>` | `fmap(f, g)` | `iso_map(f, g)` |
| `Free<F, A>` | `fmap(f)` | `map(f)` |
| `Free<F, A>` | `bind(f)`, `flat_map(f)` | `and_then(f)` |
| `Program<H, A>` | `fmap(f)` | `map(f)` |
| `Program<H, A>` | `bind(f)` | `and_then(f)` |
| `TryProgram<H, A, E>` | `fmap(f)` | `map(f)` |
| `TryProgram<H, A, E>` | `bind(f)` | `and_then(f)` |

#### Migration Examples

```rust
// Before (0.18.0)
let c = choice.fmap(|x| x * 2);
let f = free_comp.bind(|x| Free::pure(x + 1));
let flat = choice.flatten_cloned();
let age = age_lens.fmap(|n: u32| n.to_le_bytes(), |b: [u8; 4]| u32::from_le_bytes(b));

// After (0.19.0)
let c = choice.map(|x| x * 2);
let f = free_comp.and_then(|x| Free::pure(x + 1));
let flat = choice.clone().flatten();
let age = age_lens.iso_map(|n: u32| n.to_le_bytes(), |b: [u8; 4]| u32::from_le_bytes(b));
```

---

## 7. Free Monad Restructuring (`enum` → `struct`, `Then` AST Node, Internalized Erasure)

`Free<F, A>` is now an opaque struct backed by an internal `Node` enum, representing computation trees as an explicit DSL AST engine:

- **Explicit `Then` Node:** Value-independent sequencing `left.then(right)` now builds a direct `Node::Then` AST node rather than wrapping the next computation in an opaque continuation closure (`and_then`).
- **Short-circuiting:** `Pure(_).then(next)` short-circuits directly to `next` without allocating an intermediate `Then` node.
- **Inspectability Accessors:** Direct enum pattern matching (`match free { Free::Pure(..) => ... }`) is removed. Inspect AST shape via `is_pure()`, `is_suspend()`, `is_bind()`, `is_then()`, `as_pure()`, `as_suspend()`, and `as_then()`. All accessors are `pub const fn`.
- **Internalized Erasure:** `Free::into_any` is now a private implementation detail, eliminating double-erasure risks (`Arc<Arc<dyn Any>>`) with $O(1)$ fast-path cloning for already erased trees.
- **`ContStack<F>` Removed:** The orphaned type alias `ContStack<F>` is removed.

### Migration Path

```rust
// Before (0.18.0) - Pattern matching on public enum
match free_val {
    Free::Pure(val) => println!("Pure: {val}"),
    Free::Suspend(cmd, _) => println!("Suspend"),
    Free::Bind(..) => println!("Bind"),
}

// After (0.19.0) - Inherent inspectability methods
if let Some(val) = free_val.as_pure() {
    println!("Pure: {val}");
} else if let Some(cmd) = free_val.as_suspend() {
    println!("Suspend: {cmd:?}");
} else if let Some((left, right)) = free_val.as_then() {
    println!("Then sequencing");
} else if free_val.is_bind() {
    println!("Dynamic bind continuation");
}
```
