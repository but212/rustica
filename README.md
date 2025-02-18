# Rustica

[![Crates.io](https://img.shields.io/crates/v/rustica.svg)](https://crates.io/crates/rustica)
[![Documentation](https://docs.rs/rustica/badge.svg)](https://docs.rs/rustica)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Rustica is a comprehensive functional programming library for Rust, bringing powerful abstractions from category theory and functional programming to the Rust ecosystem. It provides a rich set of type classes, data types, and utilities commonly found in functional programming languages.

## Features

### Type Classes
- **Category Theory Foundations**
  - `Functor` - For mapping over contained values
  - `Applicative` - For applying functions in a context
  - `Monad` - For sequential computations
  - `Category` - For composition abstractions
  - `Arrow` - For generalized computation

- **Data Manipulation**
  - `Foldable` - For reducing structures
  - `Traversable` - For structure-preserving transformations
  - `Semigroup` & `Monoid` - For combining values

- **Advanced Concepts**
  - Higher-Kinded Types (HKT)
  - Contravariant Functors
  - Natural Transformations

### Data Types
- **Core Types**
  - `Maybe` - For optional values
  - `Either` - For error handling
  - `Choice` - For alternative computations
  - `Validated` - For accumulating errors

- **Effect Types**
  - `AsyncMonad` - For asynchronous operations
  - `IO` - For pure I/O operations
  - `State` - For stateful computations
  - `Reader` - For environment-based computations
  - `Writer` - For logging and accumulation
  - `Cont` - For continuation-based programming

- **Optics**
  - `Lens` - For focusing on parts of data structures

### Monad Transformers
- `IdentityT` - Base transformer (Work in Progress)
- More transformers planned for future releases

## Inspiration
- Inspired by Scala's Cats and Haskell's libraries.

## License
Rustica is licensed under the Apache License, version 2.0. See the [LICENSE](LICENSE) file for details.

## Documentation
For detailed documentation, please visit [docs.rs/rustica](https://docs.rs/rustica).