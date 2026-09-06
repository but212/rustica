use crate::datatypes::validated::Validated;

impl<E, A> Validated<E, A> {
    /// Maps an async function over the valid value, taking ownership.
    ///
    /// If this is valid, applies the async function to transform the value.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to the valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mapped = valid.fmap_valid_async(|x| async move { x * 2 }).await;
    /// assert_eq!(mapped, Validated::valid(84));
    /// # }
    /// ```
    pub async fn fmap_valid_async<B, F, Fut>(self, f: F) -> Validated<E, B>
    where
        F: FnOnce(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = B> + Send,
        B: Send + 'static,
    {
        match self {
            Validated::Valid(x) => {
                let result = f(x).await;
                Validated::Valid(result)
            },
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    /// Maps an async function over the error values, taking ownership.
    ///
    /// If this is invalid, applies the async function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.fmap_invalid_async(|e| async move { format!("Error: {}", e) }).await;
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// # }
    /// ```
    pub async fn fmap_invalid_async<G, F, Fut>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = G> + Send,
        G: Send + 'static,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let futures = es.into_iter().map(f);
                let results = futures::future::join_all(futures).await;
                Validated::invalid_many(results)
            },
        }
    }

    /// Chains an async validation operation, taking ownership.
    ///
    /// If this is valid, applies the async function to the value to get another Validated.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function that returns another Validated
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let chained = valid.and_then_async(|x| async move {
    ///     if x > 50 {
    ///         Validated::<&str, String>::valid(x.to_string())
    ///     } else {
    ///         Validated::<&str, String>::invalid("Value too small")
    ///     }
    /// }).await;
    ///
    /// assert_eq!(chained, Validated::<&str, String>::invalid("Value too small"));
    /// # }
    /// ```
    pub async fn and_then_async<B, F, Fut>(self, f: F) -> Validated<E, B>
    where
        F: FnOnce(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Validated<E, B>> + Send,
        B: Send + 'static,
    {
        match self {
            Validated::Valid(x) => f(x).await,
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}
