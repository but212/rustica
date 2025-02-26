use rustica::datatypes::async_monad::AsyncM;
use std::sync::Arc;

#[tokio::test]
async fn test_async_monad_pure() {
    let async_m = AsyncM::pure(42);
    let result = async_m.try_get().await;
    assert_eq!(result, 42);
}

#[tokio::test]
async fn test_async_monad_fmap() {
    let async_m = AsyncM::pure(42);
    let mapped = async_m.fmap(|x| async move { x * 2 });
    let result = mapped.try_get().await;
    assert_eq!(result, 84);
}

#[tokio::test]
async fn test_async_monad_bind() {
    let async_m = AsyncM::pure(42);
    let bound = async_m.bind(|x| async move { AsyncM::pure(x * 2) });
    let result = bound.try_get().await;
    assert_eq!(result, 84);
}

#[tokio::test]
async fn test_async_monad_apply() {
    let async_m = AsyncM::pure(42);
    let f = AsyncM::pure(Arc::new(|x: i32| x * 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    let applied = async_m.apply(f);
    let result = applied.try_get().await;
    assert_eq!(result, 84);
}

#[tokio::test]
async fn test_async_monad_chain() {
    let async_m = AsyncM::pure(42)
        .bind(|x| async move { AsyncM::pure(x + 1) })
        .bind(|x| async move { AsyncM::pure(x * 2) })
        .bind(|x| async move { AsyncM::pure(x.to_string()) });
    let result = async_m.try_get().await;
    assert_eq!(result, "86");
}

#[tokio::test]
async fn test_async_monad_with_async_fn() {
    async fn async_double(x: i32) -> i32 {
        x * 2
    }

    let async_m = AsyncM::pure(42);
    let bound = async_m.bind(|x| async move { 
        let result = async_double(x).await;
        AsyncM::pure(result)
    });
    let result = bound.try_get().await;
    assert_eq!(result, 84);
}

#[tokio::test]
async fn test_async_monad_error_handling() {
    async fn may_fail(x: i32) -> Result<i32, String> {
        if x > 0 {
            Ok(x * 2)
        } else {
            Err("Value must be positive".to_string())
        }
    }

    let success = AsyncM::pure(42)
        .bind(|x| async move {
            let result = may_fail(x).await.unwrap();
            AsyncM::pure(result)
        });
    assert_eq!(success.try_get().await, 84);

    let failure = AsyncM::pure(-1)
        .bind(|x| async move {
            let result = may_fail(x).await.unwrap_or(-1);
            AsyncM::pure(result)
        });
    assert_eq!(failure.try_get().await, -1);
}
