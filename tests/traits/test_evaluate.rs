//! Tests for the Evaluate trait

use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::traits::evaluate::{Evaluate, EvaluateExt};

mod basic_evaluate {
    use super::*;

    #[test]
    fn test_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        assert_eq!(computation.evaluate(), 42);
    }

    #[test]
    fn test_evaluate_owned() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        assert_eq!(computation.evaluate_owned(), 42);
    }

    #[test]
    fn test_evaluate_with_closure() {
        let x = 10;
        let computation: Thunk<_, i32> = Thunk::new(move || x * 2);
        assert_eq!(computation.evaluate(), 20);
    }

    #[test]
    fn test_evaluate_string() {
        let computation: Thunk<_, String> = Thunk::new(|| "hello".to_string());
        assert_eq!(computation.evaluate(), "hello".to_string());
    }
}

mod evaluate_ext_map {
    use super::*;

    #[test]
    fn test_fmap_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result: String = computation.fmap_evaluate(|x| x.to_string());
        assert_eq!(result, "42");
    }

    #[test]
    fn test_map_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result: String = computation.map_evaluate(|x| x.to_string());
        assert_eq!(result, "42");
    }

    #[test]
    fn test_fmap_evaluate_owned() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result: String = computation.fmap_evaluate_owned(|x| x.to_string());
        assert_eq!(result, "42");
    }

    #[test]
    fn test_map_evaluate_owned() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result: String = computation.map_evaluate_owned(|x| x.to_string());
        assert_eq!(result, "42");
    }

    #[test]
    fn test_map_evaluate_complex() {
        let computation: Thunk<_, Vec<i32>> = Thunk::new(|| vec![1, 2, 3]);
        let result: usize = computation.map_evaluate(|v| v.len());
        assert_eq!(result, 3);
    }
}

mod evaluate_ext_bind {
    use super::*;

    #[test]
    fn test_bind_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result = computation.bind_evaluate(|x| Thunk::new(move || x + 1));
        assert_eq!(result, 43);
    }

    #[test]
    fn test_and_then_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result = computation.and_then_evaluate(|x| Thunk::new(move || x + 1));
        assert_eq!(result, 43);
    }

    #[test]
    fn test_bind_evaluate_owned() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result = computation.bind_evaluate_owned(|x| Thunk::new(move || x + 1));
        assert_eq!(result, 43);
    }

    #[test]
    fn test_and_then_evaluate_owned() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let result = computation.and_then_evaluate_owned(|x| Thunk::new(move || x + 1));
        assert_eq!(result, 43);
    }

    #[test]
    fn test_chained_bind_evaluate() {
        let computation: Thunk<_, i32> = Thunk::new(|| 10);
        let result = computation
            .bind_evaluate(|x| Thunk::new(move || x * 2))
            .to_string();
        assert_eq!(result, "20");
    }
}

mod evaluate_ext_combine {
    use super::*;

    #[test]
    fn test_combine_evaluate() {
        let computation1: Thunk<_, i32> = Thunk::new(|| 42);
        let computation2: Thunk<_, &str> = Thunk::new(|| "answer");
        let combined = computation1.combine_evaluate(&computation2, |num, text| {
            format!("The {} is {}", text, num)
        });
        assert_eq!(combined, "The answer is 42");
    }

    #[test]
    fn test_combine_evaluate_owned() {
        let computation1: Thunk<_, i32> = Thunk::new(|| 42);
        let computation2: Thunk<_, &str> = Thunk::new(|| "answer");
        let combined = computation1
            .combine_evaluate_owned(computation2, |num, text| format!("The {} is {}", text, num));
        assert_eq!(combined, "The answer is 42");
    }

    #[test]
    fn test_combine_evaluate_arithmetic() {
        let a: Thunk<_, i32> = Thunk::new(|| 10);
        let b: Thunk<_, i32> = Thunk::new(|| 20);
        let sum = a.combine_evaluate(&b, |x, y| x + y);
        assert_eq!(sum, 30);
    }

    #[test]
    fn test_combine_evaluate_different_types() {
        let num: Thunk<_, i32> = Thunk::new(|| 5);
        let multiplier: Thunk<_, f64> = Thunk::new(|| 2.5);
        let result = num.combine_evaluate(&multiplier, |n, m| (n as f64) * m);
        assert_eq!(result, 12.5);
    }
}

mod evaluate_ext_filter {
    use super::*;

    #[test]
    fn test_filter_evaluate_pass() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let filtered: Option<i32> = computation.filter_evaluate(|&x| x > 0);
        assert_eq!(filtered, Some(42));
    }

    #[test]
    fn test_filter_evaluate_fail() {
        let computation: Thunk<_, i32> = Thunk::new(|| -10);
        let filtered: Option<i32> = computation.filter_evaluate(|&x| x > 0);
        assert_eq!(filtered, None);
    }

    #[test]
    fn test_filter_evaluate_owned_pass() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let filtered: Option<i32> = computation.filter_evaluate_owned(|&x| x > 0);
        assert_eq!(filtered, Some(42));
    }

    #[test]
    fn test_filter_evaluate_owned_fail() {
        let computation: Thunk<_, i32> = Thunk::new(|| -10);
        let filtered: Option<i32> = computation.filter_evaluate_owned(|&x| x > 0);
        assert_eq!(filtered, None);
    }

    #[test]
    fn test_filter_evaluate_complex_predicate() {
        let computation: Thunk<_, String> = Thunk::new(|| "hello".to_string());
        let filtered = computation.filter_evaluate(|s| s.len() > 3);
        assert_eq!(filtered, Some("hello".to_string()));

        let computation2: Thunk<_, String> = Thunk::new(|| "hi".to_string());
        let filtered2 = computation2.filter_evaluate(|s| s.len() > 3);
        assert_eq!(filtered2, None);
    }
}

mod idempotence_law {
    use super::*;

    #[test]
    fn test_evaluate_idempotence() {
        let computation: Thunk<_, i32> = Thunk::new(|| 42);
        let first = computation.evaluate();
        let second = computation.evaluate();
        assert_eq!(first, second);
    }

    #[test]
    fn test_referential_transparency() {
        let computation1: Thunk<_, i32> = Thunk::new(|| 42);
        let computation2: Thunk<_, i32> = Thunk::new(|| 42);
        assert_eq!(computation1.evaluate(), computation2.evaluate());
    }
}
