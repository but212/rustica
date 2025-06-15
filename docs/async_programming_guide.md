# Practical Guide: Asynchronous Programming with AsyncM

In modern applications, handling asynchronous operations like network requests, database queries, or file I/O is essential. Rust's `async/await` provides a powerful foundation, but composing and managing complex asynchronous workflows can still be challenging. Rustica's `AsyncM` provides a functional, monadic interface to make asynchronous programming more declarative, composable, and robust.

This guide will walk you through the core patterns for using `AsyncM` to manage asynchronous code effectively.

**Note:** The examples in this guide require the `tokio` runtime. Make sure you have it in your `Cargo.toml`:

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
rustica = { version = "0.8.0" }
```

## 1. What is `AsyncM`?

`AsyncM<A>` represents a computation that will produce a value of type `A` at some point in the future. It wraps an asynchronous operation, allowing you to treat it like a regular value. You can map over it, chain it with other operations, and combine multiple operations together, all without blocking or manually managing callbacks.

It implements the standard `Functor`, `Applicative`, and `Monad` type classes, providing a familiar and powerful API for functional programmers.

## 2. Creating `AsyncM` Instances

There are two primary ways to create an `AsyncM` instance.

### Using `AsyncM::pure` for Existing Values

If you already have a value and want to lift it into the asynchronous context, use `pure`. This is useful for starting a chain of operations.

```rust
use rustica::datatypes::async_monad::AsyncM;

#[tokio::main]
async fn main() {
    let async_value: AsyncM<i32> = AsyncM::pure(42);
    let result = async_value.try_get().await;

    println!("Pure value: {}", result);
    assert_eq!(result, 42);
}
```

### Using `AsyncM::new` for True Async Operations

For actual asynchronous work, you use `AsyncM::new`. It takes a closure that returns a `Future`. This is how you wrap network requests, database calls, or any other `async` block.

Let's simulate fetching data from a remote service:

```rust
use rustica::datatypes::async_monad::AsyncM;
use std::time::Duration;

// A simulated async function to fetch a user's name
async fn fetch_user_name(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(50)).await;
    format!("User-{}", user_id)
}

#[tokio::main]
async fn main() {
    let fetch_operation: AsyncM<String> = AsyncM::new(|| fetch_user_name(101));

    println!("Running fetch operation...");
    let user_name = fetch_operation.try_get().await;
    println!("Fetched user: {}", user_name);

    assert_eq!(user_name, "User-101");
}
```

Notice that `AsyncM` is lazy. The `fetch_user_name` function is not called until `try_get().await` is invoked. This allows you to build up a complex chain of operations before executing it.

## 3. Sequencing Operations with `bind`

The `bind` method (the core of the Monad pattern) is used to sequence asynchronous operations that depend on each other. It takes the result of one `AsyncM` and uses it to create the _next_ `AsyncM` in the chain.

Imagine you need to first fetch a user's ID and then use that ID to fetch their profile. The second operation depends on the first.

```rust
use rustica::datatypes::async_monad::AsyncM;
use std::time::Duration;

// Simulate fetching a user ID from an auth service
async fn fetch_user_id(username: &str) -> u32 {
    tokio::time::sleep(Duration::from_millis(50)).await;
    if username == "alice" { 101 } else { 0 }
}

// Simulate fetching user details using their ID
async fn fetch_user_details(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(50)).await;
    format!("Details for user {}", user_id)
}

#[tokio::main]
async fn main() {
    let get_user_id = AsyncM::new(|| fetch_user_id("alice"));

    // Chain the operations. The result of the first (`id`) is passed to the second.
    let get_details = get_user_id.bind(|id| async move {
        // This block returns a new AsyncM
        AsyncM::new(|| fetch_user_details(id))
    });

    println!("Fetching user details...");
    let details = get_details.try_get().await;
    println!("Result: {}", details);

    assert_eq!(details, "Details for user 101");
}
```

`bind` is the perfect tool for creating a sequential, step-by-step asynchronous workflow.

## 4. Running Operations Concurrently with `apply`

What if you have multiple asynchronous operations that _don't_ depend on each other? Running them sequentially with `bind` would be inefficient. This is where `apply` (from the Applicative pattern) shines. It allows you to run multiple `AsyncM` instances concurrently and combine their results.

Let's say you need to fetch a user's profile and their recent activity from two different services. These can happen at the same time.

```rust
use rustica::datatypes::async_monad::AsyncM;
use std::time::Duration;

// Simulate fetching user profile
async fn fetch_profile(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(100)).await;
    format!("Profile for {}", user_id)
}

// Simulate fetching user activity
async fn fetch_activity(user_id: u32) -> String {
    tokio::time::sleep(Duration::from_millis(100)).await;
    format!("Activity for {}", user_id)
}

// A function to combine the results. Note the currying.
fn combine_data(profile: String) -> impl Fn(String) -> (String, String) {
    move |activity| (profile, activity)
}

#[tokio::main]
async fn main() {
    let user_id = 101;

    // Create the two independent operations
    let get_profile = AsyncM::new(|| fetch_profile(user_id));
    let get_activity = AsyncM::new(|| fetch_activity(user_id));

    // Use `apply` to run them concurrently
    let combined_operation = AsyncM::pure(combine_data)
        .apply(get_profile)
        .apply(get_activity);

    println!("Fetching profile and activity concurrently...");
    let start = std::time::Instant::now();
    let (profile, activity) = combined_operation.try_get().await;
    let duration = start.elapsed();

    println!("Profile: '{}'", profile);
    println!("Activity: '{}'", activity);
    println!("Concurrent execution took: {:?}", duration);

    // The total time should be around 100ms, not 200ms, because they ran in parallel.
    assert!(duration < Duration::from_millis(150));
}
```

By using `apply`, we execute both `fetch_profile` and `fetch_activity` at the same time. The `join!` inside `AsyncM::apply` handles the concurrent execution. This is a powerful pattern for optimizing I/O-bound applications.

## 5. Other Useful Patterns

### Simple Transformations with `fmap`

Sometimes you don't need to chain another async operation, but simply transform the result. For this, `fmap` (from the `Functor` pattern) is a lighter-weight and more direct tool than `bind`.

```rust
use rustica::datatypes::async_monad::AsyncM;

#[tokio::main]
async fn main() {
    let get_user_id = AsyncM::pure(101);

    // Use fmap to transform the result directly
    let user_id_as_string = get_user_id.fmap(|id| async move {
        format!("User ID: {}", id)
    });

    let result = user_id_as_string.try_get().await;
    println!("{}", result);
    assert_eq!(result, "User ID: 101");
}
```

### Handling Errors with `from_result_or_default`

Asynchronous operations often involve `Result` types. `AsyncM` provides a convenient way to handle them. The `from_result_or_default` constructor will run an async operation that returns a `Result`, and if it's an `Err`, it will fall back to a default value you provide.

```rust
use rustica::datatypes::async_monad::AsyncM;

// An operation that might fail
async fn might_fail(should_succeed: bool) -> Result<String, &'static str> {
    if should_succeed {
        Ok("Success!".to_string())
    } else {
        Err("Something went wrong")
    }
}

#[tokio::main]
async fn main() {
    // Handle the success case
    let success_op = AsyncM::from_result_or_default(
        || might_fail(true),
        "Default Value".to_string()
    );
    let result1 = success_op.try_get().await;
    println!("Success case: {}", result1);
    assert_eq!(result1, "Success!");

    // Handle the failure case
    let failure_op = AsyncM::from_result_or_default(
        || might_fail(false),
        "Default Value".to_string()
    );
    let result2 = failure_op.try_get().await;
    println!("Failure case: {}", result2);
    assert_eq!(result2, "Default Value");
}
```

## Conclusion

`AsyncM` provides a powerful, functional toolkit for managing asynchronous workflows in Rust. By using these patterns, you can write code that is:

- **Declarative**: Your code describes the workflow, not the low-level mechanics of `async/await`.
- **Composable**: Small, reusable async operations can be combined into complex workflows.
- **Efficient**: `apply` allows for easy-to-read concurrent execution, optimizing performance.
- **Robust**: The monadic structure helps ensure all cases (like chaining and error handling) are managed cleanly.

Whether you are sequencing dependent API calls with `bind` or running independent queries in parallel with `apply`, `AsyncM` can help you write cleaner and more maintainable asynchronous Rust code.
