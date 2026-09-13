# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![CI](https://github.com/but212/rustica/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/but212/rustica/actions/workflows/rust.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica provides pragmatic functional programming and category theory abstractions for Rust.

## Overview

- **Type Classes**: `Functor`, `Applicative`, `Monad`, `Pure`, and `Foldable`
- **Data Types**: `Choice`, `Validated`, `Free`, and `Program` / `TryProgram`
- **Error Handling**: Context accumulation via `ContextError` and failure accumulation via `Validated`
- **Persistent Collections**: Immutable RRB-tree `PersistentVector`
- **Design Guidelines**: Adherence to Rust API Guidelines (see [docs/API_GUIDELINES.md](docs/API_GUIDELINES.md))

### Recommended Use Cases

- **Domain Modeling**: Eliminate impossible states with algebraic types (`Choice`, `Validated`)
- **Validation**: Accumulate multiple errors without early termination (`Validated`)
- **Domain DSLs**: Construct inspectable ASTs (`Free`) or statically typed command pipelines (`Program`)
- **Persistent Data**: Immutable collections with structural sharing (`PersistentVector`)

---

## Getting Started

Add Rustica to `Cargo.toml`:

```toml
[dependencies]
rustica = "0.16.0"
# Optional feature bundles:
# rustica = { version = "0.16.0", features = ["pvec"] } # persistent vectors
# rustica = { version = "0.16.0", features = ["full"] } # async, serde, quickcheck, pvec
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

- **`Choice<T>`**: Statically non-empty priority/fallback collection with deterministic fallback execution (`try_each`, `try_each_validated`).
- **`Validated<E, T>`**: Accumulates all validation errors into `NonEmptyErrors<E>`.
- **`Free<F, A>`**: Free monad separating AST construction from interpretation with stack-safe iterative trampoline execution (`run`, `try_run`, `fold_map`).
- **`Program<H, A>` / `TryProgram<H, A, E>`**: Statically-typed operational monads binding domain commands to handlers with compile-time type enforcement.
- **`PersistentVector<T>`**: Immutable vector with relaxed Radix Balanced (RRB) tree structural sharing (requires `pvec` feature).

*(Note: `Id`, `State`, `Reader`, `Writer`, `Cont`, `IO`, and Monad Transformers are deprecated in 0.17.0 in favor of native Rust primitives; see [0.17.0 Migration Guide](MIGRATION_v0.17.0.md).)*

### 3. Optics

- **`Lens`**: Pure getters and setters for product types.
- **`Prism`**: Pattern matching and traversal optics for sum types.

---

## Migration Guides

- [0.17.0 Migration Guide](MIGRATION_v0.17.0.md) (Deprecation of redundant FP abstractions in favor of native Rust primitives: Transformers, Effect Monads, FunctionCategory, Wrappers)
- [0.16.0 Migration Guide](MIGRATION_v0.16.0.md) (Choice fallback semantics, Rust API receiver alignment, optics laws, Bifunctor deprecation)
- [0.15.0 Migration Guide](MIGRATION_v0.15.0.md) (RRB tree integrity, unwrap panic context)
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

// Statically typed Operational Monad (Program)
use rustica::datatypes::operational::{Command, Handler, Program};

struct Add(i32);
impl Command for Add {
    type Output = ();
}
struct Get;
impl Command for Get {
    type Output = i32;
}

struct Calculator(i32);
impl Handler<Add> for Calculator {
    fn handle(&mut self, cmd: Add) { self.0 += cmd.0; }
}
impl Handler<Get> for Calculator {
    fn handle(&mut self, _cmd: Get) -> i32 { self.0 }
}

let program = Add(10).suspend().then(Add(5).suspend()).then(Get.suspend());
let mut calc = Calculator(0);
assert_eq!(program.run(&mut calc), 15);

// Reusable AST with Free Monad
use rustica::datatypes::free::{AnyValue, Free};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq)]
enum Op { Log(&'static str) }

let free_prog = Free::suspend(Op::Log("run1")).then(Free::suspend(Op::Log("run2")));
let mut entries = Vec::new();
free_prog.run(|op| {
    match op { Op::Log(msg) => entries.push(msg) }
    Arc::new(()) as AnyValue
});
assert_eq!(entries, vec!["run1", "run2"]);
```

---

## License

Licensed under Apache License, Version 2.0.
