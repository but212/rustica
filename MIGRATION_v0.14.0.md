# Rustica 0.14.0 Migration Guide

This document provides a guide for migrating code from Rustica 0.13.x to 0.14.0.

In Rustica 0.14.0, all APIs deprecated in 0.13.0 and their dependent traits and types have been removed to eliminate redundancy with Rust standard library types and simplify library architecture.

---

## Summary of Removals

| Deprecated / Removed in 0.14.0 | Recommended Replacement |
|---|---|
| `Maybe<T>` | Standard `Option<T>` (`rustica::traits::Functor`, `Monad`, etc. are implemented for `Option`) |
| `Either<L, R>` | Standard `Result<R, L>` or external `either` crate |
| `EitherError` | Standard `Result` pattern matching |
| `ResultEitherIso`, `either_to_result`, etc. | Standard `Result` methods |
| `Category`, `Arrow` traits | `FunctionCategory` inherent associated functions |
| `Comonad` trait | `Id<T>` inherent methods (`extract`, `duplicate`, `extend`) |
| `Evaluate`, `EvaluateExt` traits | Inherent methods (`Thunk::evaluate`, `IO::run`) |
| `ErrorPipeline`, `error_pipeline` | Native `Result` combinators + `with_context` |
| `ErrorCategory` trait | Native `Result` and `Validated` methods |
| `Pipeline<T>` | Native method chaining on `Functor` types |
| `Memoizer` | Dedicated caching crates ([`lru`](https://crates.io/crates/lru), [`moka`](https://crates.io/crates/moka)) |
| `PersistentVector::{take, skip}` | `.iter().take(n).cloned().collect()` / `.split_at(n)` |

---

## Detailed Migration Examples

### 1. `Maybe<T>` → `Option<T>`

`Maybe<T>` was a duplicate of `Option<T>`. In Rustica, `Option<T>` implements all functional traits (`Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`).

#### Before (0.13.x)
```rust
use rustica::datatypes::maybe::Maybe;
use rustica::traits::functor::Functor;

let value = Maybe::Just(42);
let doubled = value.fmap(|x| x * 2);
assert_eq!(doubled, Maybe::Just(84));

let empty: Maybe<i32> = Maybe::Nothing;
assert!(empty.is_nothing());
```

#### After (0.14.0)
```rust
use rustica::traits::functor::Functor;

let value = Some(42);
let doubled = value.fmap(|x| x * 2);
assert_eq!(doubled, Some(84));

let empty: Option<i32> = None;
assert!(empty.is_none());
```

---

### 2. `Either<L, R>` → `Result<R, L>`

#### Before (0.13.x)
```rust
use rustica::datatypes::either::Either;
use rustica::traits::functor::Functor;

let res: Either<String, i32> = Either::Right(42);
let mapped = res.fmap(|x| x + 1);
assert_eq!(mapped, Either::Right(43));

let err: Either<String, i32> = Either::Left("failed".to_string());
```

#### After (0.14.0)
```rust
use rustica::traits::functor::Functor;

let res: Result<i32, String> = Ok(42);
let mapped = res.fmap(|x| x + 1);
assert_eq!(mapped, Ok(43));

let err: Result<i32, String> = Err("failed".to_string());
```

---

### 3. Single-Implementation Traits

#### `Category` & `Arrow` → `FunctionCategory` Inherent Methods

The `Category` and `Arrow` traits are removed. `FunctionCategory` provides all morphism methods directly, and macros (`function!`, `compose!`, `pipe!`) work without trait imports.

```rust
use rustica::category::FunctionCategory;

let id_fn = FunctionCategory::identity_morphism::<i32>();
let arrow_fn = FunctionCategory::arrow(|x: i32| x * 2);
let first_fn = FunctionCategory::first::<i32, i32, &str>(&arrow_fn);
```

#### `Comonad` → `Id` Inherent Methods

```rust
use rustica::datatypes::id::Id;

let id = Id::new(42);
assert_eq!(id.extract(), 42);
let duplicated = id.duplicate();
let extended = id.extend(|i| i.extract() * 2);
```

#### `Evaluate` → Inherent Methods

```rust
use rustica::datatypes::wrapper::thunk::Thunk;

let thunk = Thunk::new(|| 42);
assert_eq!(thunk.evaluate(), &42);
assert_eq!(thunk.evaluate_owned(), 42);
```

---

### 4. Error Handling & Pipelines

#### `ErrorPipeline` → Native `Result` Combinators

```rust
use rustica::error::{ComposableError, with_context};

let result: Result<i32, &str> = Err("404");
let final_result = result
    .map(|x| x * 2)
    .map_err(|e| with_context(e, "Request failed"))
    .or_else(|_| Ok::<i32, ComposableError<&str>>(0));
```

---

### 5. Collections: `PersistentVector::{take, skip}`

```rust
use rustica::pvec::PersistentVector;

let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);

// Iterator approach
let taken: PersistentVector<i32> = vec.iter().take(3).cloned().collect();
let skipped: PersistentVector<i32> = vec.iter().skip(2).cloned().collect();

// Structural split approach (O(log n))
let (head, _) = vec.split_at(3);
let (_, tail) = vec.split_at(2);
```
