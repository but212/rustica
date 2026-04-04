use rustica::datatypes::async_monad::AsyncM;

#[tokio::test]
async fn test_core_monadic_ops() {
    // Unified verification for pure, fmap, bind, apply (both ref & owned)
    let base = AsyncM::pure(21);

    // 1. Map & Bind (Reference)
    let res_ref = base
        .fmap(|x| async move { x * 2 })
        .bind(|x| async move { AsyncM::pure(x.to_string()) })
        .try_get()
        .await;
    assert_eq!(res_ref, "42");

    // 2. Map & Bind & Apply (Owned)
    let res_owned = AsyncM::new(|| async { 21 })
        .fmap_owned(|x| async move { x * 2 })
        .bind_owned(|x| async move { AsyncM::pure(x + 10) })
        .apply_owned(AsyncM::pure(|x: i32| x.to_string()))
        .try_get()
        .await;
    assert_eq!(res_owned, "52");
}

#[tokio::test]
async fn test_async_data_pipeline() {
    // Integration of async functions, conditional branching, and chaining
    async fn async_inc(x: i32) -> i32 {
        x + 1
    }

    let pipeline = AsyncM::pure(10)
        .bind(|x| async move {
            let val = async_inc(x).await;
            if val > 0 {
                AsyncM::pure(val * 2)
            } else {
                AsyncM::pure(0)
            }
        })
        .bind_owned(|x| async move { AsyncM::pure(x.to_string()) });

    assert_eq!(pipeline.try_get().await, "22");
}

#[tokio::test]
async fn test_applicative_combination() {
    // Applicative combination with zip, zip_with, and panic resilience
    let a = AsyncM::pure(10);
    let b = AsyncM::new(|| async { "hello" });
    let combined = a
        .zip(b)
        .fmap(|(x, y)| async move { format!("{} {}", y, x) });
    assert_eq!(combined.try_get().await, "hello 10");

    // zip with panic resilience
    let panicking: AsyncM<i32> = AsyncM::new(|| async { panic!("fail") });
    let recovered = AsyncM::pure(1)
        .zip_with(panicking, |x, y| x + y)
        .recover_with(0);
    assert_eq!(recovered.try_get().await, 0);
}

#[tokio::test]
async fn test_resilience_and_helpers() {
    // Unified verification for from_result (Success/Err) and recover_with

    // 1. Success case
    let ok = AsyncM::from_result_or_default(|| async { Ok::<i32, &str>(42) }, 0);
    assert_eq!(ok.try_get().await, 42);

    // 2. Error case fallback
    let err = AsyncM::from_result_or_default(|| async { Err::<i32, &str>("error") }, 99);
    assert_eq!(err.try_get().await, 99);

    // 3. Deep panic recovery
    let deep_panic: AsyncM<i32> = AsyncM::pure(1)
        .bind(|_| async { panic!("mid-chain panic") })
        .recover_with(500);
    assert_eq!(deep_panic.try_get().await, 500);
}
