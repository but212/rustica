# Rustica Documentation

Welcome to the Rustica documentation! Rustica is a comprehensive functional programming library for Rust, focusing on creating robust, type-safe abstractions and best practices.

## Getting Started

Rustica provides a set of functional programming abstractions for Rust, including:

- Type classes like Functor, Applicative, and Monad
- Functional data types like Maybe, Either, and Validated
- Persistent immutable data structures like PersistentVector
- Utilities for functional error handling
- Tools for asynchronous functional programming

To get started with Rustica, add it to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.7.1"
```

Then import the prelude to get access to the most commonly used types and traits:

```rust
use rustica::prelude::*;
```

## Core Type Classes

Rustica implements several core type classes from functional programming:

### Functor

A functor is a type that implements a mapping operation (`fmap`) which preserves the structure of the source type while transforming its contents.

```rust
use rustica::datatypes::maybe::Maybe;
use rustica::traits::functor::Functor;

let just_five = Maybe::just(5);
let doubled = just_five.fmap(|x| x * 2);  // Maybe::Just(10)
```

### Applicative

An applicative functor is a functor with additional capabilities. It allows functions wrapped in the functor context to be applied to values in the functor context.

```rust
use rustica::datatypes::validated::Validated;
use rustica::traits::applicative::Applicative;

let valid1: Validated<&str, i32> = Validated::valid(5);
let valid2: Validated<&str, i32> = Validated::valid(10);
let combined = valid1.lift2(&valid2, |a, b| a + b);  // Validated::Valid(15)
```

### Monad

A monad is an applicative functor with additional capabilities for sequencing operations. It allows chaining operations where each step depends on the result of the previous step.

```rust
use rustica::datatypes::either::Either;
use rustica::traits::monad::Monad;

let right: Either<&str, i32> = Either::right(5);
let result = right
    .bind(|x| Either::right(x + 1))
    .bind(|x| Either::right(x * 2));  // Either::Right(12)
```

## Core Data Types

Rustica provides several functional data types:

### Maybe

`Maybe<T>` represents an optional value. It can be either `Just(T)` containing a value, or `Nothing` representing the absence of a value.

```rust
use rustica::datatypes::maybe::Maybe;

let just_value = Maybe::just(42);
let nothing_value: Maybe<i32> = Maybe::nothing();
```

### Either

`Either<L, R>` represents values with two possibilities: a value of type `L` or a value of type `R`.

```rust
use rustica::datatypes::either::Either;

let left: Either<i32, &str> = Either::left(42);
let right: Either<i32, &str> = Either::right("hello");
```

### Validated

`Validated<E, A>` represents a validation result that can either be valid with a value or invalid with a collection of errors.

```rust
use rustica::datatypes::validated::Validated;

let valid: Validated<&str, i32> = Validated::valid(42);
let invalid: Validated<&str, i32> = Validated::invalid("validation error");
```

### PersistentVector

`PersistentVector<T>` is an immutable vector implementation with memory optimization for small collections.

```rust
use rustica::pvec::{pvec, PersistentVector};

// Create using macro
let vec1 = pvec![1, 2, 3];

// Create from slice
let vec2 = PersistentVector::from_slice(&[4, 5, 6]);

// Create new vector with additional element (original unchanged)
let vec3 = vec1.push_back(4);

// Update an element (returns new vector, original unchanged)
let vec4 = vec3.update(1, 20);

// Small vectors (≤8 elements) use optimized storage
assert_eq!(vec1.get(0), Some(&1));
```

Key features:
- Memory-efficient representation for small vectors using inline storage
- Structural sharing for efficient updates and minimal copying
- O(log n) complexity for most operations
- Thread-safe due to immutability

### Choice

`Choice<T>` represents a value with multiple alternatives. It contains a primary value (the first value) and a collection of alternatives. This is useful for scenarios where you need to maintain multiple options while focusing on a primary one.

```rust
use rustica::datatypes::choice::Choice;

// Create a choice with a primary value and alternatives
let choice = Choice::new(1, vec![2, 3, 4]);

// Access the primary value
assert_eq!(choice.first(), Some(&1));

// Transform all values using the Functor trait
let doubled = choice.fmap(|x| x * 2);
assert_eq!(doubled.first(), Some(&2));

// Filter alternatives based on a predicate
let even_only = choice.filter(|x| x % 2 == 0);

// Swap the primary value with an alternative
let swapped = choice.swap_with_alternative(1);
```

The `Choice` type provides an elegant way to work with collections where one element has special significance, while maintaining the functional programming principles of immutability and explicit transformations.

## License

Rustica is licensed under the MIT License. See the [LICENSE](LICENSE) file for more information.
