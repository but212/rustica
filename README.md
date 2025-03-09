# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a comprehensive functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem. It provides a rich set of type classes, data types, and utilities commonly found in functional programming languages.

## Overview

Rustica enables idiomatic functional programming in Rust by providing:

- **Type Classes**: Core abstractions like `Functor`, `Applicative`, and `Monad`
- **Data Types**: Common functional data structures like `Maybe`, `Either`, and `IO`
- **Composable APIs**: Tools for function composition and transformation
- **Pure Functional Style**: Patterns for immutable data and explicit effect handling

Whether you're coming from Haskell, Scala, or other functional languages, or just want to explore functional programming in Rust, Rustica provides the tools you need.

## Getting Started

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.5.0"
```

If you want to use async features, add the `async` feature:

```toml
[dependencies]
rustica = { version = "0.5.0", features = ["async"] }
```

or full features:

```toml
[dependencies]
rustica = { version = "0.5.0", features = ["full"] }
```

Then import the prelude to get started:

```rust
use rustica::prelude::*;

// Example using the Maybe monad
let value = Maybe::Just(42);
let doubled = value.fmap(|x| x * 2);
assert_eq!(doubled, Maybe::Just(84));

// Example using functional composition
let add_one = |x: i32| x + 1;
let multiply_two = |x: i32| x * 2;
let composed = Either::<(), i32>::compose(&add_one, &multiply_two);
let result = composed(3); // (3 + 1) * 2 = 8
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

### Data Types

Rustica provides a rich collection of functional data types:

- **Core Types**
  - `Maybe<T>` - For optional values (like `Option<T>`)
  - `Either<L, R>` - For values with two possibilities
  - `Id<T>` - The identity monad
  - `Validated<E, T>` - For accumulating validation errors

- **Effect Types**
  - `IO<A>` - For pure I/O operations
  - `State<S, A>` - For stateful computations
  - `Reader<E, A>` - For environment-based computations
  - `Writer<W, A>` - For logging operations
  - `Cont<R, A>` - For continuation-based programming
  - `AsyncMonad<A>` - For asynchronous operations

- **Special Purpose**
  - `Choice<T>` - For representing alternative computations
  - Various wrapper types (`First`, `Last`, `Min`, `Max`, etc.)

- **Optics**
  - `Lens` - For focusing on parts of structures
  - `Prism` - For working with sum types

### Higher-Kinded Types

Rustica implements a pattern for working with higher-kinded types in Rust, providing:

- The `HKT` trait for type constructors
- The `BinaryHKT` trait for types with two parameters
- Utilities for working with HKTs

## Examples

### Working with Maybe (Option)

```rust
use rustica::prelude::*;
use rustica::datatypes::maybe::Maybe;

// Using Maybe for optional values
let input = "42";
let maybe_int = input.parse::<i32>().ok().into();  // Convert to Maybe

let result = maybe_int
    .bind(|x| if x > 0 { Maybe::Just(x) } else { Maybe::Nothing })
    .fmap(|x| x * 2);

assert_eq!(result, Maybe::Just(84));
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
