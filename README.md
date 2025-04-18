# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a comprehensive functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem. It provides a rich set of type classes, data types, and utilities commonly found in functional programming languages.

## Overview

Rustica enables idiomatic functional programming in Rust by providing:

- **Type Classes**: Core abstractions like `Functor`, `Applicative`, and `Monad`
- **Data Types**: Common functional data structures like `Maybe`, `Either`, `Choice`, and `IO`
- **Monad Transformers**: Powerful composition with `StateT`, `ReaderT`, and more
- **Composable APIs**: Tools for function composition and transformation
- **Pure Functional Style**: Patterns for immutable data and explicit effect handling
- **Error Handling**: Functional error handling utilities that work across different types

Whether you're coming from Haskell, Scala, or other functional languages, or just want to explore functional programming in Rust, Rustica provides the tools you need.

## Getting Started

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.6.4"
```

If you want to use async features, add the `async` feature:

```toml
[dependencies]
rustica = { version = "0.6.4", features = ["async"] }
```

If you want to use persistent vector collections, add the `pvec` feature:

```toml
[dependencies]
rustica = { version = "0.6.4", features = ["pvec"] }
```

You can combine multiple features as needed:

```toml
[dependencies]
rustica = { version = "0.6.4", features = ["full"] }
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
  - **PersistentVector<T>**: An efficient immutable vector with structural sharing and small vector optimization

- **Transformers**
  - `StateT<S, M, A>` - State monad transformer for combining state with other effects
  - `ReaderT<E, M, A>` - Reader monad transformer for combining environment with other effects
  - `WriterT<W, M, A>` - Writer monad transformer for combining logging with other effects
  - Bidirectional conversion between monads and their transformer versions

- **Optics**
  - `Lens` - For focusing on parts of structures
  - `Prism` - For working with sum types

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

### Persistent Collections

Rustica includes a high-performance, immutable persistent vector:

- **PersistentVector<T>**: An efficient immutable vector with structural sharing, implemented as a Relaxed Radix Balanced (RRB) tree. Provides:
  - Fast random access and updates (O(log n))
  - Small vector optimization for memory efficiency
  - Structural sharing for efficient cloning and branching
  - Customizable cache policies for advanced use cases
  - `pvec![]` macro for convenient construction

### Writer Monad with Persistent Logs

The `Writer` monad now uses `PersistentVector` for log accumulation, ensuring efficient, immutable logs with structural sharing:

- **Writer<W, A>**: Accumulates logs of type `W` alongside computations
- Efficient log accumulation and sharing

### Improved Functor Trait

- Blanket implementation for all Map trait implementers
- Ownership-aware API: `fmap_owned`, `replace_owned`, `void_owned`
- Performance: `#[inline]` on all methods
- Improved documentation and law examples

### Benchmarks and Documentation

- Comprehensive benchmarks for all data types (see [benchmarks page](https://but212.github.io/rustica/criterion/report/index.html))
- GitHub Pages documentation site: [https://but212.github.io/rustica/](https://but212.github.io/rustica/)

### Changelog

See [CHANGELOG.md](CHANGELOG.md) for a complete list of recent changes and enhancements.

## Examples

### Identity Monad (Id)

```rust
use rustica::prelude::*;
use rustica::datatypes::id::Id;
use rustica::traits::identity::Identity;

// Create Id values
let x = Id::new(5);
let y = Id::new(3);
let z = Id::new(2);

// Access the inner value using Identity trait's value() method
assert_eq!(*x.value(), 5);

// Using Functor to map over Id
let doubled = x.fmap(|n| n * 2);
assert_eq!(*doubled.value(), 10);

// Using Pure to lift a value into Id context
let pure_value = Id::<i32>::pure(&42);
assert_eq!(*pure_value.value(), 42);

// Using Applicative to apply functions
// 1. Apply a function wrapped in Id
let add_one = Id::new(|x: &i32| x + 1);
let result = x.apply(&add_one);
assert_eq!(*result.value(), 6);

// 2. Combine two Id values with lift2
let add = |a: &i32, b: &i32| a + b;
let sum = x.lift2(&y, &add);
assert_eq!(*sum.value(), 8);

// 3. Combine three Id values with lift3
let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
let product = x.lift3(&y, &z, &multiply);
assert_eq!(*product.value(), 30);

// Working with different types
let greeting = Id::new("Hello");
let count = Id::new(3_usize);
let repeat = |s: &&str, n: &usize| s.repeat(*n);
let repeated = greeting.lift2(&count, &repeat);
assert_eq!(*repeated.value(), "HelloHelloHello");

// Chaining operations
let result = x
    .fmap(|n| n + 1)     // 5 -> 6
    .fmap(|n| n * 2)     // 6 -> 12
    .fmap(|n| n.to_string());
assert_eq!(*result.value(), "12");
```

### Continuation Monad (Cont)

```rust
use rustica::datatypes::cont::Cont;

// Create a simple continuation
let cont = Cont::return_cont(42);

// Run the continuation with a handler
let result = cont.clone().run(|x| x * 2);
assert_eq!(result, 84);

// Chain continuations
let cont2 = cont.bind(|x| Cont::return_cont(x + 1));
let result2 = cont2.run(|x| x * 2);
assert_eq!(result2, 86);
```

### Control Flow Example

```rust
use std::sync::Arc;
use rustica::datatypes::cont::Cont;

// A function that uses continuations to implement early return
fn safe_divide(a: i32, b: i32) -> Cont<i32, i32> {
    if b == 0 {
        // Early return with a default value
        Cont::new(|_| -1)
    } else {
        // Continue with the division
        Cont::return_cont(a / b)
    }
}

// Run with different inputs
let result1 = safe_divide(10, 2).run(|x| x);
let result2 = safe_divide(10, 0).run(|x| x);

assert_eq!(result1, 5);
assert_eq!(result2, -1);
```

### Additional Examples from Cont

```rust
use rustica::datatypes::cont::Cont;

// Create two continuations
let cont1 = Cont::return_cont(5);
let cont2 = Cont::return_cont(-1);

// Run the continuations with an identity continuation
let result1 = cont1.run(|x| x);
let result2 = cont2.run(|x| x);

assert_eq!(result1, 5);
assert_eq!(result2, -1);
```

## Inspiration

Rustica is inspired by functional programming libraries in other languages:

- Haskell's standard library
- Scala's Cats
- Kotlin's Arrow
- TypeScript's fp-ts

## Contributing

Contributions are welcome! Check the [TODO list](TODO.md) for areas that need work.

## License

Rustica is licensed under the Apache License, version 2.0. See the [LICENSE](LICENSE) file for details.

## Documentation

For detailed documentation, please visit [docs.rs/rustica](https://docs.rs/rustica)