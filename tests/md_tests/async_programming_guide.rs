#[tokio::test]
async fn using_async_m_pure_for_existing_values() {
    use rustica::datatypes::async_monad::AsyncM;

    let async_value: AsyncM<i32> = AsyncM::pure(42);
    let result = async_value.try_get().await;

    println!("Pure value: {result}");
    assert_eq!(result, 42);
}

#[tokio::test]
async fn using_async_m_new_for_true_async_operations() {
    use rustica::datatypes::async_monad::AsyncM;
    use std::time::Duration;

    // A simulated async function to fetch a user's name
    async fn fetch_user_name(user_id: u32) -> String {
        tokio::time::sleep(Duration::from_millis(50)).await;
        format!("User-{user_id}")
    }

    let fetch_operation: AsyncM<String> = AsyncM::new(|| fetch_user_name(101));

    println!("Running fetch operation...");
    let user_name = fetch_operation.try_get().await;
    println!("Fetched user: {user_name}");

    assert_eq!(user_name, "User-101");
}

#[tokio::test]
async fn using_async_m_bind_for_chaining_operations() {
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
        format!("Details for user {user_id}")
    }

    let get_user_id = AsyncM::new(|| fetch_user_id("alice"));

    // Chain the operations. The result of the first (`id`) is passed to the second.
    let get_details = get_user_id.bind(|id| async move {
        // This block returns a new AsyncM
        AsyncM::new(move || fetch_user_details(id))
    });

    println!("Fetching user details...");
    let details = get_details.try_get().await;
    println!("Result: {details}");

    assert_eq!(details, "Details for user 101");
}

#[tokio::test]
async fn handling_errors_with_from_result_or_default() {
    use rustica::datatypes::async_monad::AsyncM;

    // An operation that might fail
    async fn might_fail(should_succeed: bool) -> Result<String, &'static str> {
        if should_succeed {
            Ok("Success!".to_string())
        } else {
            Err("Something went wrong")
        }
    }

    // Handle the success case
    let success_op =
        AsyncM::from_result_or_default(|| might_fail(true), "Default Value".to_string());
    let result1 = success_op.try_get().await;
    println!("Success case: {result1}");
    assert_eq!(result1, "Success!");

    // Handle the failure case
    let failure_op =
        AsyncM::from_result_or_default(|| might_fail(false), "Default Value".to_string());
    let result2 = failure_op.try_get().await;
    println!("Failure case: {result2}");
    assert_eq!(result2, "Default Value");
}
