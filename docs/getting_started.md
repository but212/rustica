# Getting Started with Rustica (in 30 Minutes)

Welcome to Rustica! This guide will introduce you to the core concepts of functional programming with Rustica, helping you get up and running quickly.

## 1. What is Rustica?

Rustica is a functional programming library for Rust. It provides a collection of tools, data types (like `Maybe`, `Either`, `Validated`), and type classes (like `Functor`, `Applicative`, `Monad`) to help you write more declarative, robust, and composable code in a functional style.

## 2. Why use Rustica?

- **Enhanced Readability**: Write code that is easier to understand and reason about.
- **Improved Robustness**: Leverage types to handle optional values, errors, and state in a more explicit and safe manner.
- **Better Composability**: Build complex logic by combining smaller, reusable functions and operations.
- **Embrace Immutability**: Work with data structures that don't change, reducing side effects and making concurrency easier.

## 3. Installation

### Requirements

- **Rust 1.87.0 or later** (required for Rust 2024 edition support)
- **Rust 2024 Edition** (projects must use `edition = "2024"` in Cargo.toml)

### Adding Rustica to Your Project

Add Rustica to your `Cargo.toml`:

```toml
[package]
name = "your-project"
version = "0.1.0"
edition = "2024"  # Required for Rustica 0.8.0+

[dependencies]
rustica = "0.8.0"  # Check for the latest version on crates.io
```

If you want to use specific features, add them as needed:

```toml
[dependencies]
# For async support
rustica = { version = "0.8.0", features = ["async"] }

# For persistent vector collections
rustica = { version = "0.8.0", features = ["pvec"] }

# For all features
rustica = { version = "0.8.0", features = ["full"] }
```

### Available Features

- `async`: Enables async monad support with tokio integration
- `pvec`: Includes persistent vector implementation
- `full`: Enables all features
- `quickcheck`: Enables property-based testing support

### Import the Prelude

```rust
use rustica::prelude::*;
```

## 4. Core Concept: Immutability & Pure Functions

Functional programming emphasizes **immutability** (data that doesn't change after creation) and **pure functions** (functions that always produce the same output for the same input, with no side effects).
Rust's ownership system already encourages immutability by default. Rustica builds on this by providing immutable data structures and promoting pure functions for computations.

## 5. Core Concept: Functors (e.g., `map`)

A Functor is something that can be mapped over. Think of it as a container or context, and `map` (or `fmap` in Rustica) lets you apply a function to the value(s) inside that context without changing the context itself.

### Functor Example with `Maybe` (similar to Rust's `Option`)

`Maybe<T>` represents an optional value: it can be `Just(value)` or `Nothing`.

```rust
use rustica::prelude::*;
use rustica::datatypes::maybe::Maybe;

fn main() {
    let some_number: Maybe<i32> = Maybe::Just(5);
    let doubled_number: Maybe<i32> = some_number.fmap(|x| x * 2);

    assert_eq!(doubled_number, Maybe::Just(10));

    let no_number: Maybe<i32> = Maybe::Nothing;
    let still_nothing: Maybe<i32> = no_number.fmap(|x| x * 2);

    assert_eq!(still_nothing, Maybe::Nothing);
}
```

If `some_number` was `Nothing`, `doubled_number` would also be `Nothing`. The `map` function only applies if there's a value.

## 6. Core Concept: Applicative Functors (e.g., `apply`)

An Applicative Functor builds on Functor. While `map` applies a regular function to a value in a context, `apply` applies a function that is also in a context to a value in a context. This is useful for combining multiple values that are all in a context (like `Maybe`).

### Applicative Example with `Maybe`

```rust
use rustica::prelude::*;

fn main() {
    let maybe_x = Maybe::Just(5);
    let maybe_y = Maybe::Just(3);

    let result = maybe_x.lift2(&maybe_y, |x, y| *x + *y);
    assert_eq!(result, Maybe::Just(8));

    // If any value is Nothing, the result is Nothing
    let maybe_nothing = Maybe::<i32>::Nothing;
    let nothing_result = maybe_x.lift2(&maybe_nothing, |x, y| *x + *y);
    assert_eq!(nothing_result, Maybe::Nothing);

    // Example with apply
    let maybe_add = Maybe::Just(|x: &i32| *x + 3);
    let apply_result = maybe_x.apply(&maybe_add);
    assert_eq!(apply_result, Maybe::Just(8));

    // Apply with Nothing
    let nothing_fn = Maybe::<fn(&i32) -> i32>::Nothing;
    let nothing_apply = maybe_x.apply(&nothing_fn);
    assert_eq!(nothing_apply, Maybe::Nothing);
}
```

## 7. Core Concept: Monads (e.g., `bind`)

A Monad extends Applicative with the ability to chain operations where each operation can decide what to do based on the value from the previous operation. This is particularly useful for error handling and optional values.

### Monad Example with `Maybe`

```rust
use rustica::prelude::*;

fn safe_divide(x: i32, y: i32) -> Maybe<i32> {
    if y == 0 {
        Maybe::Nothing
    } else {
        Maybe::Just(x / y)
    }
}

fn main() {
    let result = Maybe::Just(20)
        .bind(&|x: &i32| safe_divide(*x, 4))
        .bind(&|x: &i32| safe_divide(*x, 2));

    assert_eq!(result, Maybe::Just(2)); // 20 / 4 / 2 = 2

    // If any operation fails, the whole chain fails
    let failed_result = Maybe::Just(20)
        .bind(&|x: &i32| safe_divide(*x, 0)) // Division by zero
        .bind(&|x: &i32| safe_divide(*x, 2));

    assert_eq!(failed_result, Maybe::Nothing);
}
```

## 8. Advanced: Validation with Error Accumulation

The `Validated` type is great for form validation and other scenarios where you want to collect multiple errors instead of stopping at the first error.

### Example with `Validated`

```rust
use rustica::prelude::*;
use rustica::datatypes::validated::Validated;

// A curried function for creating a User
#[derive(Clone, Debug, PartialEq)]
struct User { name: String, age: u32 }
fn create_user(name: String) -> impl Fn(u32) -> User {
    move |age| User { name, age }
}

fn validate_name(name: &str) -> Validated<String, String> {
    if name.len() < 3 {
        Validated::invalid("Name must be at least 3 characters long.".to_string())
    } else {
        Validated::valid(name.to_string())
    }
}

fn validate_age(age: u32) -> Validated<String, u32> {
    if age < 18 {
        Validated::invalid("User must be at least 18 years old.".to_string())
    } else {
        Validated::valid(age)
    }
}

fn main() {
    // --- Case 1: All valid ---
    let name_input = "Alice";
    let age_input = 30;

    let user: Validated<String, User> =
        validate_name(name_input).lift2(&validate_age(age_input), |name, age| User {
            name: name.clone(),
            age: *age,
        });

    assert!(matches!(user, Validated::Valid(_)));
    println!("Valid user created: {:?}", user.unwrap());

    // --- Case 2: Multiple errors ---
    let invalid_name = "Al";
    let invalid_age = 17;

    let failed_user: Validated<String, User> =
        validate_name(invalid_name).lift2(&validate_age(invalid_age), |name, age| User {
            name: name.clone(),
            age: *age,
        });

    match failed_user {
        Validated::Invalid(errors) => {
            println!("Validation failed with {} errors:", errors.len());
            for err in errors {
                println!("- {}", err);
            }
        },
        _ => (),
    }
    // Output:
    // Validation failed with 2 errors:
    // - Name must be at least 3 characters long.
    // - User must be at least 18 years old.
}
```

Notice how we get both error messages. This is a much better user experience for things like form validation.

## 9. Where to Go Next?

Explore the rest of the library to discover more features and capabilities. Check out the [API documentation](https://docs.rs/rustica) for detailed information on all types and functions.

This was a very brief introduction! To continue your journey with Rustica:

- Dive Deeper: Read the more comprehensive TUTORIAL.md for detailed explanations of Maybe, Either, Validated, State, function composition, monad transformers, lenses, and persistent data structures.
- Explore the API: Check out the API documentation for a full list of available modules, types, and functions.
- See More Examples: Look into the examples directory in the Rustica repository or the tests and benches directories for more practical use cases.
- Learn about Type Classes: Understand Functor, Applicative, Monad, Semigroup, Monoid, and others in more detail.

## Migration from 0.7.x

If you're upgrading from a previous version:

- Update your Cargo.toml to use edition = "2024"
- Ensure you have Rust 1.87.0 or later
- Review the CHANGELOG.md for breaking changes
- Update any usage of Choice::filter vs Choice::filter_value based on your needs
- Check for any IsoLens API changes if you're using lenses

Happy functional programming with Rustica!
