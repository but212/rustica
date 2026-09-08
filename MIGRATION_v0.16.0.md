# Rustica 0.16.0 Migration Guide

This guide describes the new features, deprecations, and migration steps for Rustica 0.16.0.

## Summary of Changes

| API | Migration / Status |
| --- | --- |
| `Choice<T>` | Redefined as a statically non-empty priority/fallback collection (`primary` + ordered `alternatives`). |
| `Choice::try_each` | New execution primitive: tries `f` in priority order, returning the first `Ok` and short-circuiting on success. |
| `Choice::try_each_validated` | New execution primitive: tries `f` in priority order, accumulating all errors into `Validated<E, R>` on total failure. |
| `Choice::first_match` | New execution primitive: returns the first `Some` result in priority order. |
| `Choice::bind` | Deprecated in 0.16.0; migrate to `try_each` or explicit iterator flat-mapping. |
| `Choice::apply` | Deprecated in 0.16.0; Cartesian-product applicative operations are deprecated. |
| `impl Pure for Choice<T>` | Deprecated in 0.16.0; use `Choice::single(value)`. |
| `impl Applicative for Choice<T>` | Deprecated in 0.16.0. |
| `impl Monad for Choice<T>` | Deprecated in 0.16.0. |
| `StateT::to_state` | Deprecated in 0.16.0; renamed to `StateT::into_state` (C-CONV). |
| `ContT::to_cont` | Deprecated in 0.16.0; renamed to `ContT::into_cont` (C-CONV). |
| `WithError::to_result` | Deprecated in 0.16.0; renamed to `WithError::into_result` (C-CONV). |
| `ComposableError::set_code` | Deprecated in 0.16.0; renamed to `ComposableError::with_error_code` (C-BUILDER). |
| `Writer::log` | Breaking change: signature changed from `log(self) -> W` to `log(&self) -> &W` (C-GETTER). Migrate value consumption to `Writer::into_log(self)`. |
| `Choice::flatten` / `try_flatten` | Breaking change: receiver changed from `&self` to `self` to eliminate `Clone` bounds. Use `flatten_cloned(&self)` or `c.clone().flatten()` to preserve borrow semantics. |
| `Choice::filter` | New consuming filter eliminating `Clone` bounds; `Choice::filter_values(&self)` is deprecated. |
| `Validated::errors` | Deprecated in 0.16.0; migrate to zero-copy `error_slice(&self)` or `iter_errors(&self)`. |
| `Validated::as_ref` | Removed in 0.16.0: redundant duplicate of `as_option()`; migrate to `Validated::as_option(&self) -> Option<&A>`. |
| `datatypes::validated` submodules | Breaking change: submodules `accessors`, `conversions`, `recovery`, `async_ops` consolidated into `core`, `iter`, `combinators`, `traits`. Import from `datatypes::validated` directly. |

---

## `Validated` Module Consolidation and Breaking Removals

In 0.16.0, the `datatypes::validated` module was consolidated from 9 fragmented files into 4 cohesive submodules:

- `core`: types, constructors, safe extractors/unwraps, option views, and Result/Option conversions
- `iter`: slice views, error payloads, and iterators
- `combinators`: error mapping, sequencing, collection, recovery, and async combinators
- `traits`: type class instances

### 1. Removal of Redundant `Validated::as_ref`

The inherent method `Validated::as_ref(&self) -> Option<&A>` was removed. It was identical in behavior to `Validated::as_option(&self) -> Option<&A>` while causing naming confusion with the standard `AsRef` trait.

**Migration**:

```rust
// Old (0.15.0)
let opt = validated.as_ref();

// New (0.16.0)
let opt = validated.as_option();
```

### 2. Submodule Consolidation

The legacy submodules `rustica::datatypes::validated::{accessors, conversions, recovery, async_ops}` were removed.

**Migration**:
Import types directly from `rustica::datatypes::validated::*` (or the prelude `rustica::prelude::datatypes::*`):

```rust
// Old (0.15.0)
use rustica::datatypes::validated::accessors::*;
use rustica::datatypes::validated::conversions::*;

// New (0.16.0)
use rustica::datatypes::validated::{NonEmptyErrors, Validated};
```

---

## `Choice<T>` Redefinition: Priority and Fallback Semantics

In earlier versions, `Choice<T>` implemented `Monad` and `Applicative` as a generic non-empty list. However, Cartesian product combinations and monadic `bind` conflicted with `Choice`'s domain purpose: representing a **primary (preferred) value along with ordered fallback alternatives**.

In 0.16.0, `Choice<T>` is re-focused as a **semantic execution type** designed to guide AI agents and human developers toward writing robust, deterministic fallback logic.

### 1. Fallback Execution with `try_each`

Instead of manually extracting `primary()` or iterating over alternatives, use `try_each` to attempt operations in priority order:

```rust
use rustica::datatypes::choice::Choice;

let endpoints = Choice::new("primary.api.internal", ["backup1.api.internal", "backup2.api.internal"]);

// Tries primary first. If it fails, tries backup1, then backup2.
let connection = endpoints.try_each(|ep| connect(ep))?;
```

### 2. Error Accumulation with `try_each_validated`

When diagnosing failures across all fallback targets is required, `try_each_validated` collects every encountered error into [`Validated<E, R>`](file:///c:/Users/redog/Desktop/SJI/project/rustica/src/datatypes/validated/core.rs):

```rust
use rustica::datatypes::choice::Choice;
use rustica::datatypes::validated::Validated;

let endpoints = Choice::new("primary.api.com", ["backup.api.com"]);

match endpoints.try_each_validated(|ep| connect(ep)) {
    Validated::Valid(conn) => println!("Connected successfully!"),
    Validated::Invalid(all_errors) => {
        for err in all_errors {
            eprintln!("Endpoint attempt failed: {}", err);
        }
    }
}
```

### 3. Migrating from `Monad::bind` and `Applicative::apply`

Direct calls to `c.bind(f)` and `c.apply(v)` now emit compiler deprecation warnings.

- **If you used `bind` for fallback handling:**
  Migrate to `try_each`:

  ```rust
  // Old (0.15.0)
  // choices.bind(|x| ...);

  // New (0.16.0)
  choices.try_each(|x| ...);
  ```

- **If you used `bind` to transform elements:**
  Use `fmap` (`Functor` remains fully supported and preserves priority order):

  ```rust
  let mapped = choices.fmap(|x| x * 2);
  ```

- **If you used `Choice::pure(x)`:**
  Use `Choice::single(x)` directly:

  ```rust
  // Old (0.15.0)
  // let c = Choice::<i32>::pure(42);

  // New (0.16.0)
  let c = Choice::single(42);
  ```

---

## Semantic Changes in 0.16.0

### 1. `Vec::alt` Monoidal Concatenation

In Rustica 0.15.0 and earlier, `<Vec<T> as Alternative>::alt(a, b)` returned `a` if non-empty, otherwise `b` (first-success semantics).
In 0.16.0, `Vec::alt` implements monoidal concatenation (`a.extend(b)`), conforming to the standard monoidal alternative definition.

### 2. Transformer `apply` Polarity Inversion

`ReaderT::apply` and `ContT::apply` previously took `self` as the value and the argument as the function container (`self.apply(functions)`).
In 0.16.0, the polarity is inverted to standard Applicative convention: `self = function`, `other = value` (`functions.apply(values)`).

### 3. Ownership & Receiver Guidelines (C-CONV, C-BUILDER, C-GETTER)

In 0.16.0, receiver conventions have been strictly aligned with official Rust API Guidelines:

- **`to_*` vs `into_*`**: Consuming conversions that take `self` by value are renamed to `into_*` (`StateT::into_state`, `ContT::into_cont`, `WithError::into_result`).
- **Builder Pattern**: `ComposableError::set_code(mut self, ...)` is renamed to `with_error_code(mut self, ...)` matching `with_context`.
- **Runners vs Getters**: Methods consuming an `IO` computation to execute it (`try_get*`) are renamed to `try_run*` to avoid confusion with borrowed getters.
- **`Writer::log` Breaking Receiver Change**: `Writer::log(&self)` now returns a borrowed reference `&W` without consuming the writer. Use `Writer::into_log(self)` to consume and extract the log:

  ```rust
  let writer = Writer::new(42, vec!["init"]);

  // 0.15.0: log(self) consumed writer
  // let log = writer.log();

  // 0.16.0: log(&self) borrows
  let log_ref: &Vec<&str> = writer.log();

  // 0.16.0: into_log(self) consumes
  let owned_log: Vec<&str> = writer.into_log();
  ```

- **`Choice` Consumption & Receiver Migrations**: `Choice::filter(self)`, `Choice::flatten(self)`, and `Choice::try_flatten(self)` consume the collection by value, eliminating the `T: Clone` requirement:

  ```rust
  let nested = Choice::single(Choice::single(42));

  // 0.15.0: flatten(&self) borrowed and required T: Clone
  // let flat = nested.flatten();

  // 0.16.0: flatten(self) consumes (no Clone needed)
  let flat = nested.flatten();

  // 0.16.0: if borrowing is required, clone first or use flatten_cloned
  // let flat = nested.clone().flatten();
  // let flat = nested.flatten_cloned();
  ```

---

## Deprecations in 0.16.0 (Removal in 0.17.0)

The following traits, functions, and methods are deprecated in 0.16.0 with compiler warnings and will be removed in 0.17.0:

1. **`Iso`, `IsoExt`, `ComposedIso`, `InverseIso`, `ResultValidatedIso`**:
   Use standard Rust `From`/`Into` and `TryFrom`/`TryInto` trait conversions instead.
2. **`Bifunctor`**:
   Use inherent `bimap`/`first`/`second` methods on types or standard tuple/Result pattern matching.
3. **`FoldableExt` Search Methods**:
   `find`, `all`, `any`, `contains`, `is_sorted` on `FoldableExt` traverse the entire structure. Migrate to Rust's standard `Iterator` equivalents (`iter().find(...)`, `iter().all(...)`, etc.) for genuine short-circuit evaluation.
4. **`Alternative::many`**:
   Use standard iterator combinators or repetition instead.
5. **`FunctorExt::filter_map`, `try_map_or`, `try_map_or_else`**:
   Use standard `Iterator::filter_map` or `fmap` with `unwrap_or`/`unwrap_or_else`.
6. **`PureExt::pair_with`, `lift_other`, `combine_with`**:
   Construct values directly and lift using `Pure::pure`.
7. **`Monad::map_and_pure`, `try_bind`**:
   Use `Functor::fmap` or explicit error handling inside `bind`.
8. **`SemigroupExt::combine_all`, `combine_n` and `combine_all_values`, `combine_values`**:
   Use standard iterator folds with `combine`.
9. **`MonoidExt::is_empty_monoid`, `monoid::mconcat`, `monoid::power`**:
   Compare with `Monoid::empty()`, or use `monoid::combine_all` and `monoid::repeat`.
10. **`PersistentVector::unit`**:
    Renamed to `PersistentVector::single(value)`.
11. **`Choice::first`**:
    Renamed to `Choice::primary()`.
12. **`StateT::to_state`**:
    Renamed to `StateT::into_state` (C-CONV).
13. **`ContT::to_cont`**:
    Renamed to `ContT::into_cont` (C-CONV).
14. **`WithError::to_result`**:
    Renamed to `WithError::into_result` (C-CONV).
15. **`ComposableError::set_code`**:
    Renamed to `ComposableError::with_error_code` (C-BUILDER).
16. **`IO::try_get`, `try_get_with_context`, `try_get_composable`, `try_get_composable_with_context`**:
    Renamed to `IO::try_run*` (C-GETTER).
17. **`Choice::filter_values`**:
    Use consuming `Choice::filter` or explicit iteration/filtering.
18. **`Validated::errors`**:
    Migrate to zero-copy `Validated::error_slice` or `Validated::iter_errors`.
