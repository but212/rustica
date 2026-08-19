# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a pragmatic functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem.

## Overview

Rustica enables idiomatic functional programming in Rust by providing:

- **Type Classes**: Core abstractions like `Functor`, `Applicative`, `Monad`, `Pure`, and `Foldable`
- **Data Types**: Functional data structures like `Choice` (guaranteed non-empty alternatives), `Validated`, `Id`, and `IO`
- **Monad Transformers**: Composition with `StateT`, `ReaderT`, and `ContT`
- **Pure Functional Style**: Patterns for immutable data and explicit effect handling
- **Error Handling**: Structured context accumulation via `ComposableError` and `Validated`
- **Persistent Collections**: Efficient immutable `PersistentVector` (RRB-Tree)

### Recommended Use Cases

**Excellent for:**

- Domain modeling with compile-time impossible state elimination
- Complex validation and error accumulation (`Validated`)
- Side-effect isolation (`IO`, `State`, `Reader`)
- Learning category theory and functional programming concepts in Rust

**Avoid for:**

- Low-level, allocation-critical embedded kernel routines

---

## Getting Started

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.13.0"
```

For full features including `async`, `serde`, and `quickcheck`:

```toml
[dependencies]
rustica = { version = "0.13.0", features = ["full"] }
```

Import common traits and types through the prelude:

```rust
use rustica::prelude::*;
```

---

## Features & Core Types

### 1. Functional Type Classes

- **`Functor`** - Structure-preserving mapping (`fmap`, `fmap_owned`)
- **`Pure`** - Context-lifting (`pure`, `pure_owned`)
- **`Applicative`** - Multi-argument context application (`apply`, `lift2`, `lift3`)
- **`Monad`** - Sequential monadic chaining (`bind`, `join`)
- **`Foldable`** - Folding and aggregation (`fold_left`, `fold_right`)
- **`Semigroup` / `Monoid`** - Associative combination and identity elements

### 2. Core Data Types

- **`Choice<T>`**: Guaranteed non-empty alternatives. Statically enforces at least one primary value (`first(&self) -> &T`).
- **`Validated<E, T>`**: Accumulates all validation errors into `NonEmptyErrors<E>` without early termination.
- **`Id<T>`**: The identity functor/monad.
- **`IO<A>`**: Pure description of side-effectful computations.
- **`State<S, A>`**: Stateful computations with pure transitions.
- **`Reader<E, A>`**: Dependency injection and environment passing.
- **`Writer<W, A>`**: Computations that produce an accumulated log.
- **`Cont<R, A>`**: Continuation-passing style computations.
- **`PersistentVector<T>`**: High-performance persistent immutable vector with structural sharing.

### 3. Optics

- **`Lens`** & **`IsoLens`**: Functional getters and setters for product types.
- **`Prism`** & **`IsoPrism`**: Pattern matching and traversal optics for sum types.

---

## Deprecations in 0.13.0 (Planned for Removal in 0.14.0)

As part of the Lean Architecture initiative, redundant types and speculative wrappers are deprecated in `0.13.0` and will be completely removed in `0.14.0`:

| Deprecated Item | Recommended Replacement |
| --- | --- |
| `Maybe<T>` | `Option<T>` (already implements `Functor`, `Monad`, etc.) |
| `Either<L, R>` | `Result<R, L>` or the `either` crate |
| `Traversable` | Removed (0 implementations) |
| `Comonad` | Use `Id` methods directly |
| `Arrow` / `Category` | Native function chaining / closures |
| `Evaluate` / `EvaluateExt` | `Thunk::evaluate` directly |
| `ErrorPipeline` / `ErrorCategory` | Native `Result` method chaining (`.map()`, `.and_then()`) |
| `Pipeline<T>` | Method chaining directly on types |
| `Memoizer` | Dedicated crates like `lru` or `moka` |
| `PersistentVector::{take, skip}` | Iterator adapters (`.into_iter().take().collect()`) |

See [MIGRATION_v0.13.0.md](MIGRATION_v0.13.0.md) and [MIGRATION_v0.14.0.md](MIGRATION_v0.14.0.md) for full migration guides.

---

## Example Usage

```rust
use rustica::prelude::*;

// Functor mapping over Option
let opt = Some(42);
assert_eq!(opt.fmap(|x| x * 2), Some(84));

// Choice guarantees at least one value at compile time
let choices = Choice::new(1, [2, 3]);
assert_eq!(*choices.first(), 1);
let doubled = choices.fmap(|x| x * 2);
assert_eq!(doubled.into_iter().collect::<Vec<_>>(), vec![2, 4, 6]);

// Error accumulation with Validated
let v1: Validated<&str, i32> = Validated::valid(10);
let v2: Validated<&str, i32> = Validated::valid(20);
let sum = Validated::<&str, i32>::lift2(|a, b| *a + *b, &v1, &v2);
assert_eq!(sum, Validated::valid(30));
```

---

## License

Licensed under the Apache License, Version 2.0.
