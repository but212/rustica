#[cfg(feature = "advanced")]
mod test_cont {
    use rustica::datatypes::cont;
    use std::sync::Arc;

    #[test]
    fn test_cont_creation_and_run() {
        // Test pure creation and running
        let cont = cont::Cont::pure(42);
        let result = cont.run(|x| x * 2);
        assert_eq!(result, 84);

        // Test new creation and running
        let cont = cont::Cont::new(|k: Arc<dyn Fn(i32) -> i32>| k(42));
        let result = cont.run(|x| x * 2);
        assert_eq!(result, 84);
    }

    #[test]
    fn test_cont_functor() {
        let cont = cont::Cont::pure(42);
        let mapped = cont.fmap(|x| x + 1);
        let result = mapped.run(|x| x * 2);
        assert_eq!(result, 86);
    }

    #[test]
    fn test_cont_bind() {
        let cont = cont::Cont::pure(42);
        let bound = cont.bind(Arc::new(|x| cont::Cont::pure(x + 1)));
        let result = bound.run(|x| x * 2);
        assert_eq!(result, 86);
    }

    #[test]
    fn test_cont_apply() {
        let cont_val = cont::Cont::pure(42);
        let cont_fn =
            cont::Cont::pure(Arc::new(|x: i32| x + 1) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
        let applied = cont_val.apply(cont_fn);
        let result = applied.run(|x| x * 2);
        assert_eq!(result, 86);
    }

    #[test]
    fn test_cont_complex_composition() {
        // Create a chain of computations
        let initial = cont::Cont::pure(10);
        let step1 = initial.fmap(|x| x * 2); // 20
        let step2 = step1.bind(Arc::new(|x| cont::Cont::pure(x + 5))); // 25
        let step3 = step2.fmap(|x| x - 3); // 22

        // Run the final computation
        let result = step3.run(|x| x);
        assert_eq!(result, 22);
    }

    #[test]
    fn test_cont_error_handling() {
        // Simulate error handling with continuations
        let safe_div = |n: i32, d: i32| -> cont::Cont<String, i32> {
            if d == 0 {
                cont::Cont::new(|_| "Division by zero".to_string())
            } else {
                cont::Cont::pure(n / d)
            }
        };

        // Test successful case
        let result1 = safe_div(10, 2).run(|x| x.to_string());
        assert_eq!(result1, "5");

        // Test error case
        let result2 = safe_div(10, 0).run(|_| "Unexpected success".to_string());
        assert_eq!(result2, "Division by zero");
    }
}
