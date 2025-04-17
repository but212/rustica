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
rustica = "0.6.1"
```

If you want to use async features, add the `async` feature:

```toml
[dependencies]
rustica = { version = "0.6.1", features = ["async"] }
```

If you want to use persistent vector collections, add the `pvec` feature:

```toml
[dependencies]
rustica = { version = "0.6.1", features = ["pvec"] }
```

You can combine multiple features as needed:

```toml
[dependencies]
rustica = { version = "0.6.1", features = ["full"] }
```

Then import the prelude to get started:

```rust
use rustica::prelude::*;
use rustica::traits::composable::Composable;

fn main() {
    // Be explicit with type annotations for generic types
    let value: Maybe<i32> = Maybe::just(42);
    let doubled = value.fmap(|x| x * 2);
    assert_eq!(doubled.unwrap(), 84);

    // Example using functional composition
    let add_one = |x: i32| x + 1;
    let multiply_two = |x: i32| x * 2;
    let composed = compose(multiply_two, add_one);
    let result = composed(3); // (3 + 1) * 2 = 8
    println!("Result: {}", result);
}
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

```rust
use rustica::utils::error_utils::{traverse, sequence, ResultExt};
use rustica::datatypes::validated::Validated;

// Apply a fallible function to each element, collecting into a Result
let inputs = vec!["1", "2", "3"];
let parse_int = |s: &str| s.parse::<i32>().map_err(|_| "parse error");
let results = traverse(inputs, parse_int)?; // Results in Ok(vec![1, 2, 3])

// Combine multiple Results into one
let results_vec = vec![Ok(1), Ok(2), Ok(3)];
let combined = sequence(results_vec)?; // Results in Ok(vec![1, 2, 3])

// Convert a Result to Validated for error accumulation
let result: Result<i32, &str> = Err("Input error");
let validated: Validated<&str, i32> = result.to_validated();
```

### Persistent Collections

Rustica includes a high-performance, immutable persistent vector:

- **PersistentVector<T>**: An efficient immutable vector with structural sharing, implemented as a Relaxed Radix Balanced (RRB) tree. Provides:
  - Fast random access and updates (O(log n))
  - Small vector optimization for memory efficiency
  - Structural sharing for efficient cloning and branching
  - Customizable cache policies for advanced use cases
  - `pvec![]` macro for convenient construction

### Example Usage

```rust
use rustica::pvec::{PersistentVector, pvec};

// Create a new persistent vector
let v1: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];

// Operations return new vectors, leaving the original unchanged
let v2 = v1.push_back(6);
let v3 = v1.update(0, 10);

assert_eq!(v1.get(0), Some(&1));
assert_eq!(v2.len(), 6);
assert_eq!(v3.get(0), Some(&10));

// Use with slices
let from_slice = PersistentVector::from_slice(&[1, 2, 3]);
assert_eq!(from_slice.len(), 3);

// Advanced: custom cache policy
use rustica::pvec::{AlwaysCache};
let custom = PersistentVector::<i32>::with_cache_policy(Box::new(AlwaysCache));
assert_eq!(custom.len(), 0);
```

See the [pvec module documentation](https://docs.rs/rustica/latest/rustica/pvec/index.html) for full details.

### Enhanced Validation and Error Accumulation

Rustica's `Validated` type now uses `PersistentVector` for error accumulation, providing efficient, immutable error lists:

- **Validated<E, T>**: Represents either a valid value or a collection of errors.
  - Accumulates multiple errors (unlike `Result`, which fails fast)
  - Implements Functor, Applicative, and Monad type classes
  - Efficient error accumulation using persistent vectors

### Example

```rust
use rustica::datatypes::validated::Validated;
use rustica::pvec::PersistentVector;

let valid: Validated<&str, i32> = Validated::valid(42);
let invalid: Validated<&str, i32> = Validated::invalid("error");

// Applicative validation accumulates errors
let v1 = Validated::invalid("e1");
let v2 = Validated::invalid("e2");
let combined = v1.apply(&v2.fmap(|_| |x| x));
assert!(matches!(combined, Validated::Invalid(_)));
if let Validated::Invalid(errors) = combined {
    assert_eq!(errors.to_vec(), vec!["e1", "e2"]);
}
```

### Writer Monad with Persistent Logs

The `Writer` monad now uses `PersistentVector` for log accumulation, ensuring efficient, immutable logs with structural sharing:

- **Writer<W, A>**: Accumulates logs of type `W` alongside computations
- Efficient log accumulation and sharing

### Example

```rust
use rustica::datatypes::writer::Writer;
use rustica::pvec::PersistentVector;

let log1 = PersistentVector::from_slice(&["log1"]);
let log2 = PersistentVector::from_slice(&["log2"]);
let w1: Writer<_, i32> = Writer::new(log1, 10);
let w2: Writer<_, i32> = Writer::new(log2, 20);
let combined = w1.apply(&w2.fmap(|x| move |y| x + y));
let (log, value) = combined.run();
assert_eq!(log.to_vec(), vec!["log1", "log2"]);
assert_eq!(value, 30);
```

### Monoid Utilities

Rustica provides enhanced utilities for working with monoids:

- **MonoidExt**: Extension trait with methods like `combine_all`, `is_empty_monoid`
- **Utility Functions**:
  - `repeat(value, n)`: Combine a monoid value n times
  - `mconcat(values)`: Combine a slice of monoid values
  - `power(value, exponent)`: Raise a monoid to a power

### Example

```rust
use rustica::traits::monoid::{Monoid, MonoidExt};

#[derive(Clone, Debug, PartialEq)]
struct Sum(i32);
impl Monoid for Sum {
    fn empty() -> Self { Sum(0) }
    fn combine(&self, other: &Self) -> Self { Sum(self.0 + other.0) }
}

let values = vec![Sum(1), Sum(2), Sum(3)];
let total = MonoidExt::combine_all(&values);
assert_eq!(total, Sum(6));

let repeated = MonoidExt::repeat(Sum(2), 3);
assert_eq!(repeated, Sum(6));
```

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