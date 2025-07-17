# Rustica Tutorial: Functional Programming in Rust

This tutorial introduces functional programming concepts in Rust using the Rustica library. It's designed for developers who are new to functional programming or looking to apply these concepts in Rust.

## Table of Contents

- [Rustica Tutorial: Functional Programming in Rust](#rustica-tutorial-functional-programming-in-rust)
  - [Table of Contents](#table-of-contents)
  - [1. Introduction to Functional Programming](#1-introduction-to-functional-programming)
  - [2. Getting Started with Rustica](#2-getting-started-with-rustica)
    - [Installation](#installation)
    - [Basic Usage](#basic-usage)
  - [3. Understanding Monads](#3-understanding-monads)
  - [4. Working with Maybe (Option)](#4-working-with-maybe-option)
  - [5. Understanding Either (Result)](#5-understanding-either-result)
  - [6. Function Composition](#6-function-composition)
  - [7. Practical Examples](#7-practical-examples)
    - [Example 1: Validating User Input](#example-1-validating-user-input)
    - [Example 2: Error Handling with Either](#example-2-error-handling-with-either)
  - [8. Advanced Topics](#8-advanced-topics)
    - [Monad Transformers](#monad-transformers)
    - [Lenses](#lenses)
  - [9. Persistent Data Structures](#9-persistent-data-structures)
  - [Next Steps](#next-steps)

## 1. Introduction to Functional Programming

Functional programming is a paradigm that treats computation as the evaluation of mathematical functions and avoids changing state and mutable data. Key concepts include:

- **Pure Functions**: Functions that always produce the same output for the same input without side effects
- **Immutability**: Data structures that cannot be changed after creation
- **First-Class Functions**: Functions that can be passed around like any other value
- **Higher-Order Functions**: Functions that take other functions as parameters or return functions
- **Composition**: Building complex functions by combining simpler ones

Rust, despite being a systems language, has excellent support for functional programming through its type system, closures, and iterators.

## 2. Getting Started with Rustica

### Installation

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.8.0"
```

### Basic Usage

Import the prelude to get access to common traits and functions:

```rust
use rustica::prelude::*;
```

## 3. Understanding Monads

A monad is a design pattern that allows for sequential computation. In Rustica, monads implement the `Monad` trait, which provides methods for chaining operations.

Key monad operations:

- `pure`: Wraps a value in a monadic context
- `bind`: Chains operations that return monadic values

```rust
use rustica::prelude::*;

fn main() {
    // Create a monadic value
    let value = Maybe::Just(5);

    // Chain operations with bind
    let result = value.bind(|x| {
        if *x > 0 {
            Maybe::Just(x * 2)
        } else {
            Maybe::Nothing
        }
    });

    assert_eq!(result, Maybe::Just(10));
}
```

## 4. Working with Maybe (Option)

The `Maybe` type represents computations that might not return a value, similar to Rust's `Option`.

```rust
use rustica::prelude::*;

fn main() {
    // Creating Maybe values
    let just_value = Maybe::Just(42);
    let nothing_value = Maybe::Nothing;
    let fallback_value = 0;

    // Transforming values
    let doubled = just_value.fmap(|x| x * 2);
    assert_eq!(doubled, Maybe::Just(84));

    // Default values
    let unwrap_or_default = nothing_value.unwrap_or(&fallback_value);
    assert_eq!(*unwrap_or_default, fallback_value);

    // Chaining operations
    let result = just_value
        .bind(|x| Maybe::Just(x.to_string()))
        .bind(|s| Maybe::Just(s.to_owned() + "!"));
    assert_eq!(result, Maybe::Just("42!".to_string()));
}
```

## 5. Understanding Either (Result)

The `Either` type represents computations that might fail with an error, similar to Rust's `Result`.

```rust
use rustica::prelude::*;

fn main() {
    // Creating Either values
    let success: Either<String, i32> = Either::right(42);
    let failure: Either<String, i32> = Either::left("Error occurred".to_string());

    // Transforming values
    let doubled = success.fmap(|x| x * 2);
    assert_eq!(doubled, Either::right(84));

    // Handling errors
    let default_value = 0;
    let result = doubled.right_or(default_value);
    assert_eq!(result, 84);

    let error_result = failure.right_or(default_value);
    assert_eq!(error_result, 0);
}
```

## 6. Function Composition

Rustica provides tools for composing functions in a point-free style:

```rust
use rustica::prelude::*;
use rustica::traits::composable::compose;

fn main() {
    // Define simple functions
    let add_one = |x: i32| x + 1;
    let multiply_by_two = |x: i32| x * 2;

    // Compose functions
    let add_then_multiply = compose(add_one, multiply_by_two);

    // Use the composed function
    let result = add_then_multiply(5);
    assert_eq!(result, 12); // (5 + 1) * 2 = 12
}
```

## 7. Practical Examples

### Example 1: Validating User Input

```rust
use rustica::prelude::*;

// Validation functions
fn validate_length(input: &str) -> Maybe<String> {
    if input.len() >= 3 {
        Maybe::Just(input.to_string())
    } else {
        Maybe::Nothing
    }
}

fn validate_no_special_chars(input: &String) -> Maybe<String> {
    if input
        .chars()
        .all(|c| c.is_alphanumeric() || c.is_whitespace())
    {
        Maybe::Just(input.clone())
    } else {
        Maybe::Nothing
    }
}

fn main() {
    let username = "John Doe";

    // Chain validations
    let validation_result = Maybe::Just(username.to_string())
        .bind(|s| validate_length(&s))
        .bind(validate_no_special_chars);

    match validation_result {
        Maybe::Just(valid_name) => println!("Valid username: {valid_name}"),
        Maybe::Nothing => println!("Invalid username"),
    }
}
```

### Example 2: Error Handling with Either

```rust
use rustica::prelude::*;
use std::fs::File;
use std::io::Read;

// Function that might fail
fn read_file(path: &str) -> Either<String, String> {
    let mut file = match File::open(path) {
        Ok(file) => file,
        Err(e) => return Either::left(e.to_string()),
    };

    let mut contents = String::new();
    match file.read_to_string(&mut contents) {
        Ok(_) => Either::right(contents),
        Err(e) => Either::left(e.to_string()),
    }
}

fn main() {
    // Try to read a file
    let file_contents = read_file("example.txt");

    // Transform the contents if reading succeeded
    let processed = file_contents.fmap(|contents| contents.lines().count());

    // Handle the result
    match processed {
        Either::Right(line_count) => println!("File has {line_count} lines"),
        Either::Left(error) => println!("Error reading file: {error}"),
    }
}
```

## 8. Advanced Topics

### Monad Transformers

Monad transformers allow you to combine multiple monads. For example, `StateT` adds state to any monad:

```rust
use rustica::prelude::*;

// Define a state
type Counter = i32;

// Define a computation that increments the counter and returns a value
fn increment_and_get(amount: i32) -> StateT<Counter, Maybe<(Counter, i32)>, i32> {
    StateT::new(move |s: Counter| {
        let new_state = s + amount;
        Maybe::Just((new_state, new_state))
    })
}

fn main() {
    // Create a stateful computation
    let computation = increment_and_get(5).bind_with(
        |value| {
            // Use the value from the previous computation
            increment_and_get(value)
        },
        |m, f| m.bind(|v| f(*v)),
    );

    // Run the computation with an initial state
    let result = computation.run_state(0);

    // result is Maybe::Just((10, 10)) - our state went from 0 -> 5 -> 10
    match result {
        Maybe::Just((final_state, final_value)) => {
            println!("Final state: {final_state}, Final value: {final_value}");
        },
        Maybe::Nothing => println!("Computation failed"),
    }
}
```

### Lenses

Lenses provide a way to focus on a part of a larger data structure:

```rust
use rustica::prelude::*;

// Define a data structure
#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: i32,
}

// Define lenses for Person
fn name_lens() -> Lens<Person, String, fn(&Person) -> String, fn(Person, String) -> Person> {
    Lens::new(
        |person: &Person| person.name.clone(),
        |person: Person, new_name: String| {
            let mut new_person = person; // clone() 필요 없음
            new_person.name = new_name;
            new_person
        },
    )
}

fn age_lens() -> Lens<Person, i32, fn(&Person) -> i32, fn(Person, i32) -> Person> {
    Lens::new(
        |person: &Person| person.age,
        |person: Person, new_age: i32| {
            let mut new_person = person;
            new_person.age = new_age;
            new_person
        },
    )
}

fn main() {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };

    // Get a value using a lens
    let name = name_lens().get(&person);
    println!("Name: {name}");

    // Update a value using a lens
    let updated_person = age_lens().set(person.clone(), 31);
    println!("Updated age: {0}", updated_person.age);

    // Modify a value using a lens
    let older_person = age_lens().modify(person, |age| age + 5);
    println!("Age after 5 years: {0}", older_person.age);
}
```

## 9. Persistent Data Structures

Rustica provides immutable data structures that efficiently create modified versions through structural sharing.

```rust
use rustica::prelude::*;
use rustica::pvec::{pvec, PersistentVector};

fn main() {
    // Create a vector using the macro
    let vec1 = pvec![1, 2, 3];

    // Create a new vector with an additional element
    let vec2 = vec1.push_back(4);

    // The original vector is unchanged
    assert_eq!(vec1.len(), 3);
    assert_eq!(vec2.len(), 4);

    // Update an element
    let vec3 = vec2.update(1, 20);
    assert_eq!(vec3.get(1), Some(&20));

    // Efficient for small vectors
    let small_vec = PersistentVector::from_slice(&[1, 2, 3]);

    // Pop the last element
    if let Some((new_vec, last)) = small_vec.pop_back() {
        assert_eq!(last, 3);
        assert_eq!(new_vec.len(), 2);
    }
}
```

The `PersistentVector` implementation:

- Uses an optimized representation for small vectors (≤8 elements)
- Provides O(log n) time complexity for most operations
- Ensures efficient memory usage through structural sharing
- Is thread-safe due to its immutable nature

## Next Steps

Continue your functional programming journey with:

1. Explore more monads like `AsyncM` for asynchronous programming
2. Learn about the `Alternative` type class for computations with choice
3. Understand category theory concepts like functors, applicatives, and monads in more depth
4. Check out the full API documentation for all available functionality

Happy functional programming with Rustica!
