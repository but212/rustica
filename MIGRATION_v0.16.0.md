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
