//! Comprehensive tests for FunctionCategory implementation
use rustica::category::function_category::{FunctionCategory, function};
use rustica::traits::arrow::Arrow;
use rustica::traits::category::Category;

#[cfg(test)]
mod category_tests {
    use super::*;

    #[test]
    fn test_identity_and_composition() {
        // 1. Identity Property
        let id_int = FunctionCategory::identity_morphism::<i32>();
        assert_eq!(id_int(42), 42);
        assert_eq!(id_int(-10), -10);

        // 2. Basic & Cross-type Composition
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let to_str = FunctionCategory::arrow(|x: i32| x.to_string());
        let len = FunctionCategory::arrow(|s: String| s.len());

        let pipeline = FunctionCategory::compose_morphisms(&len, &to_str);
        let double_then_pipe = FunctionCategory::compose_morphisms(&pipeline, &double);

        assert_eq!(pipeline(123), 3); // "123".len()
        assert_eq!(double_then_pipe(5), 2); // (5*2=10) -> "10".len() = 2
    }

    #[test]
    fn test_category_laws() {
        let f = FunctionCategory::arrow(|x: i32| x + 1);
        let g = FunctionCategory::arrow(|x: i32| x * 2);
        let h = FunctionCategory::arrow(|x: i32| x - 3);
        let id = FunctionCategory::identity_morphism::<i32>();

        // Identity Laws: f ∘ id == f == id ∘ f
        let left_id = FunctionCategory::compose_morphisms(&f, &id);
        let right_id = FunctionCategory::compose_morphisms(&id, &f);

        // Associativity: (h ∘ g) ∘ f == h ∘ (g ∘ f)
        let assoc_left =
            FunctionCategory::compose_morphisms(&FunctionCategory::compose_morphisms(&h, &g), &f);
        let assoc_right =
            FunctionCategory::compose_morphisms(&h, &FunctionCategory::compose_morphisms(&g, &f));

        for i in -5..5 {
            assert_eq!(left_id(i), f(i));
            assert_eq!(right_id(i), f(i));
            assert_eq!(assoc_left(i), assoc_right(i));
        }
    }
}

#[cfg(test)]
mod arrow_tests {
    use super::*;

    #[test]
    fn test_tuple_operations() {
        let f = FunctionCategory::arrow(|x: i32| x * 2);
        let g = FunctionCategory::arrow(|x: i32| x + 1);

        // first, second
        assert_eq!(FunctionCategory::first(&f)((5, "a")), (10, "a"));
        assert_eq!(FunctionCategory::second(&f)(("a", 5)), ("a", 10));

        // split & combine (cross-types)
        let split_fg =
            FunctionCategory::split(&f, &FunctionCategory::arrow(|x: i32| x.to_string()));
        let combine_fg = FunctionCategory::combine_morphisms(&f, &g);

        assert_eq!(split_fg(5), (10, "5".to_string()));
        assert_eq!(combine_fg((5, 10)), (10, 11));
    }

    #[test]
    fn test_convenience_methods() {
        // both
        let double_both = FunctionCategory::both(|x: i32| x * 2);
        assert_eq!(double_both((3, 5)), (6, 10));

        // when
        let double_if_even = FunctionCategory::when(|x: &i32| *x % 2 == 0, |x: i32| x * 2);
        assert_eq!(double_if_even(4), 8);
        assert_eq!(double_if_even(3), 3);
    }
}

#[cfg(test)]
mod macro_and_integration_tests {
    use super::*;

    #[test]
    fn test_macro_usage_and_complex_pipeline() {
        function!(double: i32 => i32 = |x| x * 2);
        function!(to_str: i32 => String = |x: i32| x.to_string());

        let pipeline = FunctionCategory::compose_morphisms(&to_str, &double);
        assert_eq!(pipeline(21), "42");

        // Logic branching via 'when'
        let safe_pipe = FunctionCategory::compose_morphisms(
            &FunctionCategory::arrow(|x: i32| format!("Val: {}", x)),
            &FunctionCategory::when(|x: &i32| *x > 0, |x: i32| x * 10),
        );
        assert_eq!(safe_pipe(5), "Val: 50");
        assert_eq!(safe_pipe(-5), "Val: -5");
    }

    #[test]
    fn test_arc_safety_and_stress() {
        // Arc sharing
        let f = FunctionCategory::arrow(|x: i32| x * x).clone();
        assert_eq!(f(3), 9);

        // Deep composition stress
        let mut deep = FunctionCategory::arrow(|x: i32| x + 1);
        for _ in 0..100 {
            deep = FunctionCategory::compose_morphisms(&deep, &FunctionCategory::arrow(|x| x + 1));
        }
        assert_eq!(deep(0), 101);
    }
}
