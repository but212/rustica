# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![CI](https://github.com/but212/rustica/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/but212/rustica/actions/workflows/rust.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica provides pragmatic functional programming and category theory abstractions for Rust.

## Overview

- **Type Classes**: `Functor`, `Applicative`, `Monad`, `Pure`, and `Foldable`
- **Data Types**: `Choice` (statically non-empty priority/fallback collection), `Validated`, `Id`, and `IO`
- **Monad Transformers**: `StateT`, `ReaderT`, and `ContT`
- **Error Handling**: Context accumulation via `ContextError` and failure accumulation via `Validated`
- **Persistent Collections**: Immutable RRB-tree `PersistentVector`
- **Design Guidelines**: Strict adherence to Rust API Guidelines (see [docs/API_GUIDELINES.md](docs/API_GUIDELINES.md))

### Recommended Use Cases

- **Domain Modeling**: Eliminate impossible states at compile time
- **Validation**: Accumulate multiple errors without early termination (`Validated`)
- **Effect Isolation**: Manage state, dependencies, and I/O explicitly (`IO`, `State`, `Reader`)
- **Persistent Data**: Immutable collections with structural sharing (`PersistentVector`)

---

## Getting Started

Add Rustica to `Cargo.toml`:

```toml
[dependencies]
rustica = "0.16.0"
```

Enable all features (`async`, `serde`, `quickcheck`, and `pvec`):

```toml
[dependencies]
rustica = { version = "0.16.0", features = ["full"] }
```

Or enable persistent vector support selectively:

```toml
[dependencies]
rustica = { version = "0.16.0", features = ["pvec"] }
```

Import common traits and types:

```rust
use rustica::prelude::*;
```

---

## Core Features and Types

### 1. Functional Type Classes

- **`Functor`**: Structure-preserving mapping (`fmap`)
- **`Pure`**: Context lifting (`pure`)
- **`Applicative`**: Multi-argument application (`apply`, `lift2`, `lift3`)
- **`Monad`**: Sequential chaining (`bind`, `join`)
- **`Foldable`**: Traversal and aggregation (`fold_left`, `fold_right`)
- **`Semigroup` / `Monoid`**: Associative combination and identity elements

### 2. Core Data Types

- **`Choice<T>`**: Statically non-empty priority/fallback collection. Provides `try_each`, `try_each_validated`, and `first_match` for deterministic fallback execution.
- **`Validated<E, T>`**: Accumulates all validation errors into `NonEmptyErrors<E>`.
- **`Id<T>`**: Identity functor and monad with comonad operations (`extract`, `duplicate`, `extend`).
- **`IO<A>`**: Cold, side-effectful computations evaluated via `run` or `try_run`.
- **`State<S, A>`**: Pure state transitions (`run_state`, `eval_state`, `exec_state`).
- **`Reader<E, A>`**: Environment inspection and dependency passing.
- **`Writer<W, A>`**: Pure logging with monoidal log accumulation (`log`, `into_log`).
- **`Cont<R, A>`**: Continuation-passing style computation (`run`).
- **`Free<F, A>`**: Free monad separating AST construction from interpretation with stack-safe iterative trampoline execution (`run`, `try_run`, `fold_map`).
- **`Program<H, A>` / `TryProgram<H, A, E>`**: Statically-typed operational monads binding domain `Command`s to handler traits (`Handler<C>`, `TryHandler<C, E>`) with zero-downcast compile-time type enforcement and stack-safe execution.
- **`PersistentVector<T>`**: Immutable vector with relaxed Radix Balanced (RRB) tree structural sharing (requires `pvec` feature).

### 3. Optics

- **`Lens`**: Pure getters and setters for product types.
- **`Prism`**: Pattern matching and traversal optics for sum types.

---

## Migration Guides

- [0.16.0 Migration Guide](MIGRATION_v0.16.0.md) (Choice fallback semantics, Rust API receiver alignment, Applicative polarity)
- [0.16.0 Migration Guide](MIGRATION_v0.15.0.md) (RRB tree integrity, unwrap panic context)
- [0.14.0 Migration Guide](MIGRATION_v0.14.0.md) (Surface reduction, compile-time base monad enforcement)

---

## Development and CI

Rustica requires Rust 1.88.0 or newer.

```bash
cargo fmt --all -- --check
cargo clippy --all-targets --all-features --locked -- -D warnings
cargo test --all-features --locked
cargo package --all-features --locked
```

Pull requests run read-only quality, platform, and MSRV checks. Releases are published automatically from verified `v*` tags with SLSA provenance. Report vulnerabilities per [SECURITY.md](.github/SECURITY.md).

---

## Example Usage

```rust
use rustica::prelude::*;

// Functor mapping over Option
let opt = Some(42);
assert_eq!(opt.fmap(|x| x * 2), Some(84));

// Choice: guaranteed non-empty priority/fallback execution
let endpoints = Choice::new("primary.api.com", ["backup1.api.com", "backup2.api.com"]);
assert_eq!(*endpoints.primary(), "primary.api.com");
let connected = endpoints.try_each(|ep| {
    if *ep == "backup1.api.com" { Ok("connected") } else { Err("unreachable") }
});
assert_eq!(connected, Ok("connected"));

// Error accumulation with Validated
let v1: Validated<&str, i32> = Validated::valid(10);
let v2: Validated<&str, i32> = Validated::valid(20);
let sum = Validated::<&str, i32>::lift2(|a, b| a + b, v1, v2);
assert_eq!(sum, Validated::valid(30));
```

---

## License

Licensed under Apache License, Version 2.0.
