#[cfg(feature = "async")]
mod test_async_monad {
    use rustica::datatypes::async_monad::AsyncM;

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

        // Test with owned values
        let async_m_owned = AsyncM::pure(42);
        let mapped_owned = async_m_owned.fmap_owned(|x| async move { x.to_string() });
        let result_owned = mapped_owned.try_get().await;
        assert_eq!(result_owned, "42");
    }

    #[tokio::test]
    async fn test_async_monad_bind() {
        let async_m = AsyncM::pure(42);
        let bound = async_m.bind(|x| async move { AsyncM::pure(x * 2) });
        let result = bound.try_get().await;
        assert_eq!(result, 84);

        // Test with owned values
        let async_m_owned = AsyncM::pure(42);
        let bound_owned = async_m_owned.bind_owned(|x| async move { AsyncM::pure(x.to_string()) });
        let result_owned = bound_owned.try_get().await;
        assert_eq!(result_owned, "42");
    }

    #[tokio::test]
    async fn test_async_monad_apply() {
        let async_m = AsyncM::pure(42);
        let f = AsyncM::pure(|x: i32| x * 2);
        let applied = async_m.apply(f);
        let result = applied.try_get().await;
        assert_eq!(result, 84);

        // Test with owned values
        let async_m_owned = AsyncM::pure(42);
        let f_owned = AsyncM::pure(|x: i32| x.to_string());
        let applied_owned = async_m_owned.apply(f_owned);
        let result_owned = applied_owned.try_get().await;
        assert_eq!(result_owned, "42");
    }

    #[tokio::test]
    async fn test_async_monad_chain() {
        let async_m = AsyncM::pure(42)
            .bind(|x| async move { AsyncM::pure(x + 1) })
            .bind(|x| async move { AsyncM::pure(x * 2) })
            .bind(|x| async move { AsyncM::pure(x.to_string()) });
        let result = async_m.try_get().await;
        assert_eq!(result, "86");

        // Test with owned values
        let async_m_owned = AsyncM::pure(42)
            .bind_owned(|x| async move { AsyncM::pure(x + 1) })
            .bind_owned(|x| async move { AsyncM::pure(x * 2) })
            .bind_owned(|x| async move { AsyncM::pure(x.to_string()) });
        let result_owned = async_m_owned.try_get().await;
        assert_eq!(result_owned, "86");
    }

    #[tokio::test]
    async fn test_async_monad_with_async_function() {
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

        // Test with owned values
        let async_m_owned = AsyncM::pure(42);
        let bound_owned = async_m_owned.bind_owned(|x| async move {
            let result = async_double(x).await;
            AsyncM::pure(result)
        });
        let result_owned = bound_owned.try_get().await;
        assert_eq!(result_owned, 84);
    }

    #[tokio::test]
    async fn test_async_monad_error_handling() {
        async fn may_fail(x: i32) -> Result<i32, &'static str> {
            if x < 0 {
                Err("Negative value")
            } else {
                Ok(x * 2)
            }
        }

        let success = AsyncM::pure(42).bind(|x| async move {
            let result = may_fail(x).await.unwrap();
            AsyncM::pure(result)
        });
        assert_eq!(success.try_get().await, 84);

        // Test with owned values
        let success_owned = AsyncM::pure(42).bind_owned(|x| async move {
            let result = may_fail(x).await.unwrap();
            AsyncM::pure(result)
        });
        assert_eq!(success_owned.try_get().await, 84);

        let failure = AsyncM::pure(-1).bind(|x| async move {
            let result = may_fail(x).await.unwrap_or(-1);
            AsyncM::pure(result)
        });
        assert_eq!(failure.try_get().await, -1);
    }

    #[tokio::test]
    async fn test_async_monad_from_result_or_default() {
        // Test success case
        async fn success_fn() -> Result<i32, &'static str> {
            Ok(42)
        }

        let success = AsyncM::from_result_or_default(success_fn, 0);
        assert_eq!(success.try_get().await, 42);

        // Test error case
        async fn error_fn() -> Result<i32, &'static str> {
            Err("error")
        }

        let error = AsyncM::from_result_or_default(error_fn, 100);
        assert_eq!(error.try_get().await, 100);
    }
}
