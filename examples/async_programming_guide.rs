//! # Async Programming Guide
//!
//! This example demonstrates async programming patterns with Rustica.
//! Note: This example requires the "async" feature to be enabled.
//!
//! Run with: `cargo run --example async_programming_guide --features async`

#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;

#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
// Simulate an async operation
async fn fetch_user_data(user_id: u32) -> Result<String, String> {
    tokio::time::sleep(Duration::from_millis(50)).await;
    if user_id == 1 {
        Ok("Alice".to_string())
    } else {
        Err("User not found".to_string())
    }
}

#[cfg(feature = "async")]
async fn fetch_user_posts(user_id: u32) -> Result<Vec<String>, String> {
    tokio::time::sleep(Duration::from_millis(30)).await;
    if user_id == 1 {
        Ok(vec!["Post 1".to_string(), "Post 2".to_string()])
    } else {
        Err("Posts not found".to_string())
    }
}

#[cfg(feature = "async")]
async fn fetch_user_profile(user_id: u32) -> Result<String, String> {
    tokio::time::sleep(Duration::from_millis(20)).await;
    Ok(format!("Profile for user {}", user_id))
}

#[cfg(feature = "async")]
// Main async function demonstrating async monadic operations
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== AsyncM Examples ===\n");

    // Example 1: Basic usage with pure values
    println!("1. Basic AsyncM with pure values:");
    let async_number = AsyncM::pure(42);
    let result = async_number.try_get().await;
    println!("   Result: {}\n", result);

    // Example 2: Creating AsyncM from async operations
    println!("2. Creating AsyncM from async operations:");
    let fetch_operation = AsyncM::new(|| fetch_user_id("alice"));
    let user_id = fetch_operation.try_get().await;
    println!("   User ID: {}\n", user_id);

    // Example 3: Sequencing operations with bind
    println!("3. Sequencing operations with bind:");
    let get_user_profile = AsyncM::new(|| fetch_user_id("bob"))
        .bind(|id| async move { AsyncM::new(move || fetch_user_profile(id)) });

    let profile = get_user_profile.try_get().await;
    println!("   Profile: {}\n", profile);

    // Example 4: Complex chaining
    println!("4. Complex operation chaining:");
    let complex_operation = AsyncM::new(|| fetch_user_id("alice"))
        .bind(|user_id| async move {
            println!("   Fetched user ID: {}", user_id);
            AsyncM::new(move || fetch_user_profile(user_id))
        })
        .bind(|profile| async move {
            println!("   Fetched profile: {}", profile);
            AsyncM::pure(format!("Processed: {}", profile))
        });

    let final_result = complex_operation.try_get().await;
    println!("   Final result: {}\n", final_result);

    // Example 5: Error handling with from_result_or_default
    println!("5. Error handling with from_result_or_default:");

    // Success case
    let success_case =
        AsyncM::from_result_or_default(|| fetch_user_avatar(101), "default_avatar.png".to_string());
    let avatar1 = success_case.try_get().await;
    println!("   Success case: {}", avatar1);

    // Failure case
    let failure_case =
        AsyncM::from_result_or_default(|| fetch_user_avatar(0), "default_avatar.png".to_string());
    let avatar2 = failure_case.try_get().await;
    println!("   Failure case: {}", avatar2);

    println!("\n=== All examples completed successfully! ===");
    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("Async Programming Guide");
    println!("This example requires the 'async' feature to be enabled.");
    println!("Run with: cargo run --example async_programming_guide --features async");
    println!("");
    println!("The async feature provides:");
    println!("- AsyncM monad for composing async operations");
    println!("- Monadic error handling with async/await");
    println!("- Functional composition of async computations");
    println!("");
    println!("Without the async feature, this example demonstrates the concept");
    println!("but cannot run the actual async code.");
}
