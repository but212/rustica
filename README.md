# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a comprehensive functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem. It provides a rich set of type classes, data types, and utilities commonly found in functional programming languages.

## Overview

Rustica enables idiomatic functional programming in Rust by providing:

- **Type Classes**: Core abstractions like `Functor`, `Applicative`, and `Monad`
- **Data Types**: Common functional data structures like `Maybe`, `Either`, `Choice`, and `IO`
- **Composable APIs**: Tools for function composition and transformation
- **Pure Functional Style**: Patterns for immutable data and explicit effect handling
- **Error Handling**: Functional error handling utilities that work across different types

Whether you're coming from Haskell, Scala, or other functional languages, or just want to explore functional programming in Rust, Rustica provides the tools you need.

## Getting Started

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.5.4"
```

If you want to use async features, add the `async` feature:

```toml
[dependencies]
rustica = { version = "0.5.4", features = ["async"] }
```

or full features:

```toml
[dependencies]
rustica = { version = "0.5.4", features = ["full"] }
```

Then import the prelude to get started:

```rust
use rustica::prelude::*;
use rustica::traits::composable::Composable;

fn main() {
    // Be explicit with type annotations for generic types
    let value: Maybe<i32> = Maybe::Just(42);
    let doubled = value.fmap(|x| x * 2);
    assert_eq!(doubled.unwrap(), 84);

    // Example using functional composition
    let add_one = |x: i32| x + 1;
    let multiply_two = |x: i32| x * 2;
    let composed = Either::<(), i32>::compose(&add_one, &multiply_two);
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
  - `State<S, A>` - For stateful computations
  - `Reader<E, A>` - For environment-based computations
  - `Writer<W, A>` - For logging operations
  - `Cont<R, A>` - For continuation-based programming
  - `AsyncMonad<A>` - For asynchronous operations

- **Special Purpose**
  - Various wrapper types (`First`, `Last`, `Min`, `Max`, etc.)

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
use rustica::traits::functor::Functor;

// Using Maybe for optional values with explicit type annotations
let input = "42";
let maybe_int: Maybe<i32> = input.parse::<i32>().ok().into();  // Convert to Maybe

let result = maybe_int
    .bind(|x: i32| if x > 0 { Maybe::Just(x) } else { Maybe::Nothing })
    .fmap(|x: i32| x * 2);

assert_eq!(result, Maybe::Just(84));
```

### Working with Choice for non-deterministic computations

```rust
use rustica::prelude::*;
use rustica::datatypes::choice::Choice;
use rustica::traits::functor::Functor;
use rustica::traits::applicative::Applicative;

// Create a Choice with a primary value and alternatives
let numbers: Choice<i32> = Choice::new(2, vec![3, 4, 5]);

// Map over all possible values
let doubled: Choice<i32> = numbers.fmap(|x| x * 2);
assert_eq!(*doubled.first().unwrap(), 4);  // Primary value is 2*2=4
assert_eq!(doubled.alternatives(), &[6, 8, 10]);  // Alternatives are [3*2, 4*2, 5*2]

// Apply functions with applicative
let add_one = |x: &i32| x + 1;
let multiply_by_three = |x: &i32| x * 3;
let functions = Choice::new(add_one, vec![multiply_by_three]);

let results = numbers.apply(&functions);
// Primary result is add_one(2) = 3
// Alternatives include all combinations of functions and values
```

### Error Handling with Validated

```rust
use rustica::prelude::*;
use rustica::utils::error_utils::traverse_validated;
use rustica::datatypes::validated::Validated;

// Define validation functions
let validate_positive = |x: i32| -> Result<i32, String> {
    if x > 0 {
        Ok(x)
    } else {
        Err(format!("Value must be positive: {}", x))
    }
};

let validate_even = |x: i32| -> Result<i32, String> {
    if x % 2 == 0 {
        Ok(x)
    } else {
        Err(format!("Value must be even: {}", x))
    }
};

// Validate multiple values, collecting all errors
let inputs = vec![10, -5, 7, 8];
let validation_result = traverse_validated(inputs, |x| {
    let x = validate_positive(x)?;
    validate_even(x)
});

// Check if validation passed or inspect all errors
match validation_result {
    Validated::Valid(values) => println!("All values valid: {:?}", values),
    _ => {
        println!("Validation errors:");
        for error in validation_result.errors() {
            println!("  - {}", error);
        }
    }
}
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