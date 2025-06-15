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

Add Rustica to your `Cargo.toml`:

```toml
[dependencies]
rustica = "0.7.1" # Check for the latest version on crates.io
```

And import the prelude in your Rust files to get access to common traits and types:

```rust
use rustica::prelude::*;
```

## 4. Core Concept: Immutability & Pure Functions

Functional programming emphasizes **immutability** (data that doesn't change after creation) and **pure functions** (functions that always produce the same output for the same input, with no side effects).

Rust's ownership system already encourages immutability by default. Rustica builds on this by providing immutable data structures and promoting pure functions for computations.

## 5. Core Concept: Functors (e.g., `map`)

A Functor is something that can be mapped over. Think of it as a container or context, and `map` (or `fmap` in Rustica) lets you apply a function to the value(s) inside that context without changing the context itself.

**Example with `Maybe` (similar to Rust's `Option`):**

`Maybe<T>` represents an optional value: it can be `Just(value)` or `Nothing`.

```rust
use rustica::prelude::*;
use rustica::datatypes::maybe::Maybe;

fn main() {
    let some_number: Maybe<i32> = Maybe::just(5);
    let doubled_number: Maybe<i32> = some_number.map(|x| x * 2); // or .fmap(|x| x * 2)

    assert_eq!(doubled_number, Maybe::just(10));

    let no_number: Maybe<i32> = Maybe::nothing();
    let still_nothing: Maybe<i32> = no_number.map(|x| x * 2);

    assert_eq!(still_nothing, Maybe::nothing());
}
```

If `some_number` was `Nothing`, `doubled_number` would also be `Nothing`. The `map` function only applies if there's a value.

## 6. Core Concept: Applicative Functors (e.g., `apply`)

An Applicative Functor builds on Functor. While `map` applies a regular function to a value in a context, `apply` applies a _function that is also in a context_ to a value in a context. This is useful for combining multiple values that are all in a context (like `Maybe`).

**Example with `Maybe`:**

Let's say we have a function that takes two arguments, and we have two `Maybe` values we want to use with it.

```rust
use rustica::prelude::*;
use rustica::datatypes::maybe::Maybe;

// A curried function for addition
fn add(a: i32) -> impl Fn(i32) -> i32 {
    move |b| a + b
}

fn main() {
    let maybe_five: Maybe<i32> = Maybe::just(5);
    let maybe_ten: Maybe<i32> = Maybe::just(10);

    // First, we map `add` over the first Maybe.
    // This gives us a function inside a Maybe: Maybe<impl Fn(i32) -> i32>
    let maybe_add_five = maybe_five.map(add);

    // Now, we use `apply` to apply the function inside `maybe_add_five`
    // to the value inside `maybe_ten`.
    let result: Maybe<i32> = maybe_ten.apply(&maybe_add_five);

    assert_eq!(result, Maybe::just(15));

    // If either is Nothing, the result is Nothing.
    let maybe_nothing: Maybe<i32> = Maybe::nothing();
    let result_fail = maybe_nothing.apply(&maybe_add_five);

    assert_eq!(result_fail, Maybe::nothing());
}
```

This might seem complex, but it's the foundation for powerful patterns, like collecting multiple validation errors, which we'll see later with the `Validated` type.

## 7. Core Concept: Monads (e.g., `bind`)

A Monad allows you to sequence computations, especially when those computations themselves return a value in a context (like `Maybe` or `Either`). The key operation is `bind` (or `and_then` in some contexts).

**Example with `Maybe`:**

Imagine you have two functions that might fail (return `Nothing`):

```rust
use rustica::prelude::*;
use rustica::datatypes::maybe::Maybe;

fn try_parse(s: &str) -> Maybe<i32> {
    s.parse().ok().into() // .into() converts Option<i32> to Maybe<i32>
}

fn check_positive(n: i32) -> Maybe<i32> {
    if n > 0 { Maybe::just(n) } else { Maybe::nothing() }
}

fn main() {
    let input_str = "10";

    // Chain the operations using bind
    let result: Maybe<i32> = try_parse(input_str)
        .bind(|parsed_num| check_positive(parsed_num));

    assert_eq!(result, Maybe::just(10));

    let invalid_input_str = "-5";
    let result_fail: Maybe<i32> = try_parse(invalid_input_str)
        .bind(|parsed_num| check_positive(parsed_num));

    // try_parse("-5") is Just(-5), then check_positive(-5) is Nothing
    assert_eq!(result_fail, Maybe::nothing());
}
```

If `try_parse` returns `Nothing`, `check_positive` is never called, and the whole chain results in `Nothing`. `bind` handles the 'short-circuiting'.

## 8. A Glimpse into State Management: The `State` Monad

How do we handle state (like a counter or a game score) in a world of immutable data and pure functions? The `State` monad is the answer. A `State<S, A>` represents a computation that takes an initial state `S` and produces a result `A` along with a new state `S`.

**Example: A Simple Counter**

Let's build a sequence of operations that increments a counter and returns logs of the operations.

```rust
use rustica::prelude::*;
use rustica::datatypes::state::State;

fn main() {
    // A computation that increments the state and returns the new state as its result.
    let increment = State::modify(|s: &i32| s + 1).bind(|_| State::get());

    // A computation that doubles the state and returns the new state.
    let double = State::modify(|s: &i32| s * 2).bind(|_| State::get());

    // Chain the operations together using bind
    let program = increment
        .bind(|_first_val| double)
        .bind(|_second_val| increment);

    // To run the computation, we provide an initial state.
    // `run_state` returns both the final state and the final result.
    let initial_state = 5;
    let (final_state, final_result) = program.run_state(initial_state);

    // Initial: 5
    // 1. increment: 5 + 1 = 6. State is 6.
    // 2. double: 6 * 2 = 12. State is 12.
    // 3. increment: 12 + 1 = 13. State is 13.
    assert_eq!(final_state, 13);
    assert_eq!(final_result, 13); // The last operation's result was the state itself

    println!("Final state: {}", final_state);
}
```

This allows you to build complex stateful logic in a composable way without using mutable variables.

## 9. Practical Example: Accumulating Errors with `Validated`

While `Either` (or `Result`) is great for fail-fast validation, what if you want to show the user _all_ the errors at once? This is where `Validated<E, A>` and the Applicative Functor pattern shine.

`Validated` can be `Valid(value)` or `Invalid(errors)`. When combining `Validated` instances using the Applicative `apply` method, it accumulates errors instead of short-circuiting.

```rust
use rustica::prelude::*;
use rustica::datatypes::validated::Validated;

// A curried function for creating a User
#[derive(Debug, PartialEq)]
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
        Validated::valid(create_user)
            .apply(validate_name(name_input))
            .apply(validate_age(age_input));

    assert!(matches!(user, Validated::Valid(_)));
    println!("Valid user created: {:?}", user.unwrap());

    // --- Case 2: Multiple errors ---
    let invalid_name = "Al";
    let invalid_age = 17;

    let failed_user: Validated<String, User> =
        Validated::valid(create_user)
            .apply(validate_name(invalid_name))
            .apply(validate_age(invalid_age));

    match failed_user {
        Validated::Invalid(errors) => {
            println!("Validation failed with {} errors:", errors.len());
            for err in errors {
                println!("- {}", err);
            }
        }
        _ => ()
    }
    // Output:
    // Validation failed with 2 errors:
    // - Name must be at least 3 characters long.
    // - User must be at least 18 years old.
}
```

Notice how we get both error messages. This is a much better user experience for things like form validation.

## 10. Where to Go Next?

This was a very brief introduction! To continue your journey with Rustica:

- **Dive Deeper**: Read the more comprehensive [TUTORIAL.md](./TUTORIAL.md) for detailed explanations of `Maybe`, `Either`, `Validated`, `State`, function composition, monad transformers, lenses, and persistent data structures.
- **Explore the API**: Check out the [API documentation](https://docs.rs/rustica/) (link to your actual API docs) for a full list of available modules, types, and functions.
- **See More Examples**: Look into the `examples` directory in the Rustica repository (if available) or the `tests` and `benches` directories for more practical use cases.
- **Learn about Type Classes**: Understand `Functor`, `Applicative`, `Monad`, `Semigroup`, `Monoid`, and others in more detail.

Happy functional programming with Rustica!
