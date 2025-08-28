#![cfg(feature = "async")]

use rustica::datatypes::async_monad::AsyncM;
use std::time::Duration;
use tokio;

#[tokio::test]
async fn test_async_monad_cancellation() {
    // Create an AsyncM that will never resolve, to simulate a long-running task.
    let long_running_task = AsyncM::new(|| async {
        tokio::time::sleep(Duration::from_secs(10)).await;
        42
    });

    let handle = tokio::spawn(async move {
        long_running_task
            .bind(|x| async move { AsyncM::pure(x + 1) })
            .try_get()
            .await
    });

    // Abort the task almost immediately.
    handle.abort();

    // The aborted task should result in an error.
    let result = handle.await;
    assert!(result.is_err());
    assert!(result.unwrap_err().is_cancelled());
}
