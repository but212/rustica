# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![CI](https://github.com/but212/rustica/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/but212/rustica/actions/workflows/rust.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](./LICENSE)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/but212/rustica)

Rustica provides functional programming and categorical abstractions for Rust, designed for zero-cost domain modeling where standard library primitives leave gaps.

## Overview

### Recommended Use Cases

- **Domain Modeling**: Precise state representation via algebraic types (`Choice`, `Validated`).
- **Validation**: Multi-error accumulation without early return (`Validated`).
- **Domain DSLs**: AST construction (`Free`) or statically typed command dispatch (`Program` / `TryProgram`).
- **Optics**: Ergonomic immutable access and transformation for complex structs and enums (`Lens`, `Prism`).

Architecture and conventions:

- **Design Philosophy**: Architectural trade-offs and boundary guidelines ([docs/DESIGN_RATIONALE.md](docs/DESIGN_RATIONALE.md)).
- **API Guidelines**: Naming, receiver standards, and ownership conventions ([docs/API_GUIDELINES.md](docs/API_GUIDELINES.md)).

---

## Getting Started

Add Rustica to `Cargo.toml`:

```toml
[dependencies]
rustica = "0.18.0"
# Features:
# rustica = { version = "0.18.0", features = ["full"] } # async (deprecated in 0.19.0), serde, quickcheck
```

> [!NOTE]
> The current released version on crates.io is `0.18.0`. Ongoing breaking changes and modernization for the upcoming `0.19.0` release are documented in the [0.19.0 Migration Guide](./MIGRATION_v0.19.0.md).

Import common traits and types:

```rust
use rustica::prelude::*;
```

---

## Core Features

### 1. Algebraic Structures

- **`Semigroup`**: Associative combination via `combine`.
- **`Monoid`**: Identity elements and empty sequence aggregation via `empty` and `combine_all`.

### 2. Core Data Types

- **`Choice<T>`**: Guaranteed non-empty priority and fallback execution sequence (`try_each`, `try_each_validated`).
- **`Validated<T, E>`**: Multi-error accumulation into `NonEmptyErrors<E>` with applicative zip and iterator collection.
- **`Free<F, A>`**: Free monad DSL AST engine with explicit `Then` sequencing, bounded recursion, and stack-safe iterative execution (`run`, `try_run`).
- **`Program<H, A>` / `TryProgram<H, A, E>`**: Single-threaded operational monads (`Box`-backed) with compile-time handler signatures, native `Rc`/`RefCell` support, and stack-safe trampoline evaluation.

### 3. Optics

- **`Lens`**: Composable getters, setters, and modifiers for product types (`get`, `set`, `modify`, `then`).
- **`Prism`**: Pattern matching optics for sum types (`preview`, `review`, `set`, `modify`, `then`).

---

## Migration Guides

- [0.19.0 Migration Guide](./MIGRATION_v0.19.0.md): Free monad restructuring (`enum` → `struct`, explicit `Then` AST node, internal type-erasure), operational monad single-threaded decoupling (`Send + Sync` removal for `Rc`/`RefCell`), removal of PersistentVector (`pvec`), categorical simulation traits (`HKT`, `Functor`, `Pure`, `Applicative`, `Monad`, `Foldable`), and `Prism::set_if_different`
- [0.18.0 Migration Guide](./MIGRATION_v0.18.0.md): Removal of deprecated modules (Transformers, Effect Monads, Category, Wrappers, Legacy Errors)
- [0.17.0 Migration Guide](./MIGRATION_v0.17.0.md): Deprecation of monad transformers, effect monads, category morphisms, and wrapper types in favor of standard library idioms
- [0.16.0 Migration Guide](./MIGRATION_v0.16.0.md): Choice fallback semantics, receiver alignment, optics laws, Bifunctor deprecation
- [0.15.0 Migration Guide](./MIGRATION_v0.15.0.md): RRB tree integrity and panic context
- [0.14.0 Migration Guide](./MIGRATION_v0.14.0.md): Surface reduction and compile-time base monad enforcement

---

## Development and CI

Rustica requires Rust 1.88.0 or newer.

```bash
cargo fmt --all -- --check
cargo clippy --all-targets --all-features --locked -- -D warnings
cargo test --all-features --locked
cargo package --all-features --locked
```

PRs run read-only quality, platform, and MSRV checks. Releases publish automatically from verified `v*` tags with SLSA provenance. Report vulnerabilities via [SECURITY.md](.github/SECURITY.md).

---

## Example Usage

```rust
use rustica::prelude::*;

// Semigroup combination
let left = vec![1, 2];
let right = vec![3, 4];
assert_eq!(left.combine(right), vec![1, 2, 3, 4]);

// Choice: guaranteed non-empty priority/fallback execution
let endpoints = Choice::new("primary.api.com", ["backup1.api.com", "backup2.api.com"]);
assert_eq!(*endpoints.primary(), "primary.api.com");
let connected = endpoints.try_each(|ep| {
    if *ep == "backup1.api.com" { Ok("connected") } else { Err("unreachable") }
});
assert_eq!(connected, Ok("connected"));

// Error accumulation with Validated (inherent zip & collect)
let v1: Validated<i32, &str> = Validated::valid(10);
let v2: Validated<i32, &str> = Validated::valid(20);
assert_eq!(v1.zip_with(v2, |a, b| a + b), Validated::valid(30));

let items = vec![Validated::<i32, &str>::valid(1), Validated::valid(2)];
let collected: Validated<Vec<i32>, &str> = items.into_iter().collect();
assert_eq!(collected, Validated::valid(vec![1, 2]));

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

let free_prog: Free<Op, ()> =
    Free::<Op, ()>::suspend(Op::Log("run1")).then(Free::suspend(Op::Log("run2")));
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
