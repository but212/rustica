# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![CI](https://github.com/but212/rustica/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/but212/rustica/actions/workflows/rust.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica brings pragmatic functional-programming and category-theory abstractions to Rust.

## Overview

Rustica provides:

- **Type Classes**: `Functor`, `Applicative`, `Monad`, `Pure`, and `Foldable`
- **Data Types**: `Choice` (guaranteed non-empty alternatives), `Validated`, `Id`, and `IO`
- **Monad Transformers**: `StateT`, `ReaderT`, and `ContT`
- **Pure Functional Style**: Immutable data and explicit effects
- **Error Handling**: Context accumulation with `ComposableError` and `Validated`
- **Persistent Collections**: Immutable RRB-tree `PersistentVector`

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
rustica = "0.14.0"
```

For full features including `async`, `serde`, and `quickcheck`:

```toml
[dependencies]
rustica = { version = "0.14.0", features = ["full"] }
```

Import common traits and types through the prelude:

```rust
use rustica::prelude::*;
```

---

## Features & Core Types

### 1. Functional Type Classes

- **`Functor`** - Structure-preserving mapping (`fmap`)
- **`Pure`** - Context-lifting (`pure`)
- **`Applicative`** - Multi-argument context application (`apply`, `lift2`, `lift3`)
- **`Monad`** - Sequential monadic chaining (`bind`, `join`)
- **`Foldable`** - Folding and aggregation (`fold_left`, `fold_right`)
- **`Semigroup` / `Monoid`** - Associative combination and identity elements

### 2. Core Data Types

- **`Choice<T>`**: Guaranteed non-empty alternatives. Statically enforces at least one primary value (`first(&self) -> &T`).
- **`Validated<E, T>`**: Accumulates all validation errors into `NonEmptyErrors<E>` without early termination.
- **`Id<T>`**: The identity functor/monad with inherent comonad methods (`extract`, `duplicate`, `extend`).
- **`IO<A>`**: Pure description of side-effectful computations.
- **`State<S, A>`**: Stateful computations with pure transitions.
- **`Reader<E, A>`**: Dependency injection and environment passing.
- **`Writer<W, A>`**: Computations that produce an accumulated log.
- **`Cont<R, A>`**: Continuation-passing style computations.
- **`PersistentVector<T>`**: High-performance persistent immutable vector with structural sharing.

### 3. Optics

- **`Lens`**: Functional getters and setters for product types. Build one from an `Iso` with `Lens::from_iso`.
- **`Prism`**: Pattern matching and traversal optics for sum types. Build one from an `Iso` with `Prism::from_iso`.

---

## Migration from 0.13 to 0.14

`0.14.0` removes redundant types (`Maybe`, `Either`), single-implementation
traits (`Category`, `Arrow`, `Comonad`, `Evaluate`), and speculative wrappers
(`ErrorPipeline`, `ErrorCategory`, `Memoizer`). `ReaderT` and `StateT` enforce
base-monad value types at compile time; standard `Result`, `Iterator`, and
`From` APIs replace duplicate error helpers.

See [MIGRATION_v0.14.0.md](MIGRATION_v0.14.0.md) for the migration guide.

The unreleased 0.15.0 breaking changes are documented in
[MIGRATION_v0.15.0.md](MIGRATION_v0.15.0.md).

---

## Development and CI

Rustica requires Rust 1.88.0 or newer. Before opening a pull request, run CI's
core checks:

```bash
cargo fmt --all -- --check
cargo clippy --all-targets --all-features --locked -- -D warnings
cargo test --all-features --locked
cargo package --all-features --locked
```

Pull requests run read-only quality, platform, and MSRV checks. Weekly or
manual workflows run nightly tests, unused-dependency checks, and Miri.
Benchmarks are available locally through Cargo's benchmark tooling and are not
run as part of CI.

`v*` tags create releases after validating the tag version, Cargo metadata, and
matching `CHANGELOG.md` section. The protected `crates-io` environment controls
publishing, and releases receive SLSA provenance. Report vulnerabilities as
instructed in [SECURITY.md](.github/SECURITY.md).

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
let sum = Validated::<&str, i32>::lift2(|a, b| a + b, v1, v2);
assert_eq!(sum, Validated::valid(30));
```

---

## License

Licensed under the Apache License, Version 2.0.
