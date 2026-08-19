# Rustica 0.14 Migration Plan (Notice for Deprecated Items in 0.13.0)

This document provides early guidance for migrating code using APIs that were deprecated in `0.13.0` and will be completely removed in `0.14.0`.

## Planned Removals in 0.14.0

### 1. `Maybe<T>` → `Option<T>`
- **Reason**: `Maybe<T>` is a 1:1 duplicate of Rust's standard `Option<T>`. `Option<T>` already implements all FP traits (`Functor`, `Monad`, `Applicative`, `Foldable`).
- **Migration**:
  - Replace `Maybe::Just(x)` with `Some(x)`
  - Replace `Maybe::Nothing` with `None`
  - Replace `Maybe<T>` type annotations with `Option<T>`

### 2. `Either<L, R>` → `Result<R, L>` or `either::Either`
- **Reason**: `Either<L, R>` is isomorphic to `Result<R, L>`. The ecosystem-standard `either` crate is recommended for non-error branching.
- **Migration**:
  - Replace `Either::Right(r)` with `Ok(r)`
  - Replace `Either::Left(l)` with `Err(l)`
  - Use `either` crate directly if non-result sum semantics are desired.

### 3. Single-Implementation Traits
- **`Comonad`**: Only implemented for `Id`. Call `.extract()` or `.run()` directly on `Id`.
- **`Arrow` & `Category`**: Only implemented for `FunctionCategory`. Use function chaining or closures directly.
- **`Evaluate` & `EvaluateExt`**: Only implemented for `Thunk`. Call `thunk.evaluate()` directly.

### 4. Over-Engineered Wrappers
- **`ErrorPipeline`**: Use native `Result` combinators (`.map()`, `.and_then()`, `.map_err()`).
- **`ErrorCategory`**: Use `Result` standard methods.
- **`Pipeline<T>`**: Use native method chaining.
- **`Memoizer`**: Use dedicated production caching crates such as [`lru`](https://crates.io/crates/lru) or [`moka`](https://crates.io/crates/moka).

### 5. `PersistentVector` Collection Iterators
- **`PersistentVector::{take, skip}`**: Use standard iterator adapters: `.into_iter().take(n).collect()` or `.iter().skip(n).collect()`.
