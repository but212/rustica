# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a comprehensive functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem. It provides a rich set of type classes, data types, and utilities commonly found in functional programming languages.

## IMPORTANT PERFORMANCE NOTICE

**This library prioritizes correctness and learning over performance. Current implementations have 20-100x overhead compared to direct Rust code, making them unsuitable for production performance-critical applications.**

## Overview

Rustica enables idiomatic functional programming in Rust by providing:

- **Type Classes**: Core abstractions like `Functor`, `Applicative`, and `Monad`
- **Data Types**: Common functional data structures like `Maybe`, `Either`, `Choice`, and `IO`
- **Monad Transformers**: Powerful composition with `StateT`, `ReaderT`, and more
- **Composable APIs**: Tools for function composition and transformation
- **Pure Functional Style**: Patterns for immutable data and explicit effect handling
- **Error Handling**: Functional error handling utilities that work across different types

### Recommended Use Cases

**Excellent for:**

- Learning functional programming concepts
- Prototyping and research
- Educational purposes
- Small-scale applications

**Avoid for:**

- Performance-critical production code
- Real-time systems
- Game engines
- High-throughput web servers

Whether you're coming from Haskell, Scala, or other functional languages, or just want to explore functional programming in Rust, Rustica provides the tools you need for learning and experimentation.

## Getting Started

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.10.0"
```

If you want to use async features, add the `async` feature:

```toml
[dependencies]
rustica = { version = "0.10.0", features = ["async"] }
```

Persistent vector collections are now included by default in Rustica 0.10.0.

You can combine multiple features as needed:

```toml
[dependencies]
rustica = { version = "0.10.0", features = ["full"] }
```

Then import the prelude to get started:

```rust
use rustica::prelude::*;
```

## Features

### Type Classes

Rustica implements a wide range of type classes from category theory:

- **Basic Abstractions**
  - `Functor` - For mapping over contained values
  - `Applicative` - For applying functions in a context
  - `Monad` - For sequential computations
  - `Pure` - For lifting values into a context
  - `Identity` - For accessing values inside contexts
  - `Alternative` - For choice between computations

- **Algebraic Structures**
  - `Semigroup` - Types with an associative binary operation
  - `Monoid` - Semigroups with an identity element
  - `Foldable` - For reducing structures
  - `Traversable` - For structure-preserving transformations

- **Advanced Concepts**
  - `Bifunctor` - For mapping over two type parameters
  - `Contravariant` - For reversing function application
  - `Category` - For abstract composition
  - `Arrow` - For generalized computation
  - `Comonad` - For context-aware computations
  - `MonadError` - For error handling in monadic contexts

### Data Types

Rustica provides a rich collection of functional data types:

- **Core Types**
  - `Maybe<T>` - For optional values (like `Option<T>`)
  - `Either<L, R>` - For values with two possibilities
  - `Id<T>` - The identity monad
  - `Validated<E, T>` - For accumulating validation errors
  - `Choice<T>` - For representing non-deterministic computations with alternatives

- **Effect Types**
  - `IO<A>` - For pure I/O operations
  - `State<S, A>` - For stateful computations with thread-safe implementations
  - `Reader<E, A>` - For environment-based computations
  - `Writer<W, A>` - For logging operations
  - `Cont<R, A>` - For continuation-based programming
  - `AsyncMonad<A>` - For asynchronous operations

- **Special Purpose**
  - Various wrapper types (`First`, `Last`, `Min`, `Max`, etc.)

- **Persistent Collections**
  - `PersistentVector<T>` - An efficient immutable vector with structural sharing and small vector optimization

- **Transformers**
  - `StateT<S, M, A>` - State monad transformer for combining state with other effects
  - `ReaderT<E, M, A>` - Reader monad transformer for combining environment with other effects
  - `WriterT<W, M, A>` - Writer monad transformer for combining logging with other effects
  - Bidirectional conversion between monads and their transformer versions

- **Optics**
  - `Lens` - For focusing on parts of structures
  - `Prism` - For working with sum types
  - `IsoLens` - Lawful, composable lenses based on isomorphisms for deep focusing
  - `IsoPrism` - Lawful, composable prisms based on isomorphisms for sum types

### Error Handling Utilities

Rustica provides standardized error handling utilities that work across different functional types:

- **Core Functions**
  - `sequence` - Combines a collection of `Result` values into a single `Result` containing a collection
  - `traverse` - Applies a function that produces a `Result` to a collection, returning a single `Result`
  - `traverse_validated` - Like `traverse` but collects all errors instead of failing fast

- **Type Conversion**
  - `ResultExt` trait - Extends `Result` with methods like `to_validated()` and `to_either()`
  - `WithError` trait - Generic trait for any type that can represent error states
  - Conversion functions between `Result`, `Either`, and `Validated`

- **Error Types**
  - `AppError<M, C>` - A structured error type that provides both a message and optional context
  - Helper functions like `error()` and `error_with_context()`

### Persistent Vector

Rustica provides an immutable persistent vector (RRB-Tree) for functional programming patterns. This is included by default in Rustica 0.10.0.

Example Usage

```rust
use rustica::pvec::PersistentVector;
use rustica::pvec::pvec;

let v1: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];
let v2 = v1.push_back(6);
let v3 = v1.update(0, 10);

assert_eq!(v1.get(0), Some(&1));
assert_eq!(v2.get(5), Some(&6));
assert_eq!(v3.get(0), Some(&10));
```

### CI/CD & Publishing

Rustica uses GitHub Actions for continuous integration, formatting, linting, and automated publishing to crates.io on tagged releases.

- Tests and formatting are run on every push and pull request.
- When a tag (e.g. `v0.10.0`) is pushed, the version is checked and, if not already published, is automatically uploaded to crates.io.

### Changelog

See [CHANGELOG.md](CHANGELOG.md) for a complete list of recent changes and enhancements.

## Examples

### Basic Usage

```rust
use rustica::prelude::*;

// Working with Maybe (like Option)
let maybe_value = Maybe::Just(42);
let doubled = maybe_value.fmap(|x| x * 2);
assert_eq!(doubled.unwrap(), 84);

// Working with Either for error handling
let result: Either<String, &str> = Either::Right("success");
let processed = result.fmap(|s| s.to_uppercase());
assert_eq!(processed.unwrap(), "SUCCESS");

// Using Choice for multiple alternatives
let choices = Choice::new(1, [2, 3]);
let results = choices.fmap(|x| x * 2);
assert_eq!(results.iter().collect::<Vec<_>>(), vec![&2, &4, &6]);
```

### State Management

```rust
use rustica::datatypes::state::State;

// A simple counter
let counter = State::new(|count: i32| (count + 1, count));

// Run the state computation
let (new_count, result) = counter.run_state(0);
assert_eq!(new_count, 1);
assert_eq!(result, 0);
```

### IO Operations

```rust
use rustica::datatypes::io::IO;

// Pure IO description
let read_line = IO::new(|| "Hello from IO!".to_string());

// Execute the IO operation
let result = read_line.run();
assert_eq!(result, "Hello from IO!");
```

## Inspiration

Rustica is inspired by functional programming libraries in other languages:

- Haskell's standard library
- Scala's Cats
- Kotlin's Arrow
- TypeScript's fp-ts

## License

Rustica is licensed under the Apache License, version 2.0. See the [LICENSE](LICENSE) file for details.

## Documentation

For detailed documentation, please visit [docs.rs/rustica](https://docs.rs/rustica)
