# Practical Guide: Asynchronous Programming with AsyncM

In modern applications, handling asynchronous operations like network requests, database queries, or file I/O is essential. Rust's `async/await` provides a powerful foundation, but composing and managing complex asynchronous workflows can still be challenging. Rustica's `AsyncM` provides a functional, monadic interface to make asynchronous programming more declarative, composable, and robust.

This guide will walk you through the core patterns for using `AsyncM` to manage asynchronous code effectively.

**Note:** The examples in this guide require the `tokio` runtime and the "async" feature to be enabled. Make sure you have it in your `Cargo.toml`:

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
rustica = { version = "0.9.0", features = ["async"] }
```

**Running the Examples:**

To run the async programming guide example:

```bash
cargo run --example async_programming_guide --features async
```

If the async feature is not enabled, the example will display information about the async functionality without running the actual async code.

## 1. What is `AsyncM`?

`AsyncM<A>` represents a computation that will produce a value of type `A` at some point in the future. It wraps an asynchronous operation, allowing you to treat it like a regular value. You can map over it, chain it with other operations, and combine multiple operations together, all without blocking or manually managing callbacks.

It implements the standard `Functor`, `Applicative`, and `Monad` type classes, providing a familiar and powerful API for functional programmers.

**Feature Requirement:** `AsyncM` is only available when the "async" feature is enabled. This is done to keep the core library lightweight for users who don't need async functionality.

## 2. Creating `AsyncM` Instances

There are two primary ways to create an `AsyncM` instance.

### Using `AsyncM::pure` for Existing Values

If you already have a value and want to lift it into the asynchronous context, use `pure`. This is useful for starting a chain of operations.

```rust
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() {
    let async_value: AsyncM<i32> = AsyncM::pure(42);
    let result = async_value.try_get().await;
    // result is 42
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("This example requires the 'async' feature to be enabled.");
    println!("Run with: cargo run --example async_programming_guide --features async");
}
```

### Using `AsyncM::new` for True Async Operations

For actual asynchronous work, you use `AsyncM::new`. It takes a closure that returns a `Future`. This is how you wrap network requests, database calls, or any other `async` block.

Let's simulate fetching data from a remote service:

```rust
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
// A simulated async function to fetch a user's name
async fn fetch_user_name(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(50)).await;
    format!("User-{user_id}")
}

#[cfg(feature = "async")]
#[tokio::main]
async fn main() {
    let fetch_operation: AsyncM<String> = AsyncM::new(|| fetch_user_name(101));
    let user_name = fetch_operation.try_get().await;
    // user_name is "User-101"
}
```

Notice that `AsyncM` is lazy. The `fetch_user_name` function is not called until `try_get().await` is invoked. This allows you to build up a complex chain of operations before executing it.

## 3. Sequencing Operations with `bind`

The `bind` method (the core of the Monad pattern) is used to sequence asynchronous operations that depend on each other. It takes the result of one `AsyncM` and uses it to create the _next_ `AsyncM` in the chain.

Imagine you need to first fetch a user's ID and then use that ID to fetch their profile. The second operation depends on the first.

```rust
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
// Simulate fetching a user ID from an auth service
async fn fetch_user_id(username: &str) -> u32 {
    tokio::time::sleep(Duration::from_millis(50)).await;
    if username == "alice" { 101 } else { 0 }
}

#[cfg(feature = "async")]
// Simulate fetching user details using their ID
async fn fetch_user_details(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(50)).await;
    format!("Details for user {user_id}")
}

#[cfg(feature = "async")]
#[tokio::main]
async fn main() {
    let get_user_id = AsyncM::new(|| fetch_user_id("alice"));

    // Chain the operations. The result of the first (`id`) is passed to the second.
    let get_details = get_user_id.bind(|id| async move {
        // This block returns a new AsyncM
        AsyncM::new(move || fetch_user_details(id))
    });

    let details = get_details.try_get().await;
    // details is "Details for user 101"
}
```

`bind` is the perfect tool for creating a sequential, step-by-step asynchronous workflow.

## 4. Other Useful Patterns

### Handling Errors with `from_result_or_default`

Asynchronous operations often involve `Result` types. `AsyncM` provides a convenient way to handle them. The `from_result_or_default` constructor will run an async operation that returns a `Result`, and if it's an `Err`, it will fall back to a default value you provide.

```rust
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;

#[cfg(feature = "async")]
// An operation that might fail
async fn might_fail(should_succeed: bool) -> Result<String, &'static str> {
    if should_succeed {
        Ok("Success!".to_string())
    } else {
        Err("Something went wrong")
    }
}

#[cfg(feature = "async")]
#[tokio::main]
async fn main() {
    // Handle the success case
    let success_op =
        AsyncM::from_result_or_default(|| might_fail(true), "Default Value".to_string());
    let result1 = success_op.try_get().await;
    // result1 is "Success!"

    // Handle the failure case
    let failure_op =
        AsyncM::from_result_or_default(|| might_fail(false), "Default Value".to_string());
    let result2 = failure_op.try_get().await;
    // result2 is "Default Value"
}
```

## Conclusion

`AsyncM` provides a powerful, functional toolkit for managing asynchronous workflows in Rust. By using these patterns, you can write code that is:

- **Declarative**: Your code describes the workflow, not the low-level mechanics of `async/await`.
- **Composable**: Small, reusable async operations can be combined into complex workflows.
- **Efficient**: `apply` allows for easy-to-read concurrent execution, optimizing performance.
- **Robust**: The monadic structure helps ensure all cases (like chaining and error handling) are managed cleanly.

Whether you are sequencing dependent API calls with `bind` or running independent queries in parallel with `apply`, `AsyncM` can help you write cleaner and more maintainable asynchronous Rust code.
