//! Comprehensive tests for FunctionCategory implementation
//!
//! This module contains thorough tests for all aspects of the FunctionCategory
//! implementation, including Category laws, Arrow laws, and practical usage scenarios.

use rustica::category::function_category::{FunctionCategory, function};
use rustica::traits::arrow::Arrow;
use rustica::traits::category::Category;

/// Test basic Category trait implementation
#[cfg(test)]
mod category_tests {
    use super::*;

    #[test]
    fn test_identity_morphism() {
        let id_int = FunctionCategory::identity_morphism::<i32>();
        let id_string = FunctionCategory::identity_morphism::<String>();

        // Test identity property
        assert_eq!(id_int(42), 42);
        assert_eq!(id_string("hello".to_string()), "hello");
        assert_eq!(id_int(-100), -100);
        assert_eq!(id_string("".to_string()), "");
    }

    #[test]
    fn test_basic_composition() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let add_one = FunctionCategory::arrow(|x: i32| x + 1);

        // Test composition: (add_one ∘ double)(x) = add_one(double(x))
        let composed = FunctionCategory::compose_morphisms(&add_one, &double);

        assert_eq!(composed(5), 11); // double(5) = 10, add_one(10) = 11
        assert_eq!(composed(0), 1); // double(0) = 0, add_one(0) = 1
        assert_eq!(composed(-3), -5); // double(-3) = -6, add_one(-6) = -5
    }

    #[test]
    fn test_left_identity_law() {
        // Left identity: f ∘ id = f
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let id = FunctionCategory::identity_morphism::<i32>();

        let composed = FunctionCategory::compose_morphisms(&double, &id);

        // Should behave exactly like the original function
        for i in -10..10 {
            assert_eq!(composed(i), double(i));
        }
    }

    #[test]
    fn test_right_identity_law() {
        // Right identity: id ∘ f = f
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let id = FunctionCategory::identity_morphism::<i32>();

        let composed = FunctionCategory::compose_morphisms(&id, &double);

        // Should behave exactly like the original function
        for i in -10..10 {
            assert_eq!(composed(i), double(i));
        }
    }

    #[test]
    fn test_associativity_law() {
        // Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
        let f = FunctionCategory::arrow(|x: i32| x + 1);
        let g = FunctionCategory::arrow(|x: i32| x * 2);
        let h = FunctionCategory::arrow(|x: i32| x - 3);

        // Left association: (h ∘ g) ∘ f
        let goh = FunctionCategory::compose_morphisms(&h, &g);
        let left_assoc = FunctionCategory::compose_morphisms(&goh, &f);

        // Right association: h ∘ (g ∘ f)
        let gof = FunctionCategory::compose_morphisms(&g, &f);
        let right_assoc = FunctionCategory::compose_morphisms(&h, &gof);

        // Should produce the same results
        for i in -5..5 {
            assert_eq!(left_assoc(i), right_assoc(i));
        }
    }

    #[test]
    fn test_different_types_composition() {
        let int_to_string = FunctionCategory::arrow(|x: i32| x.to_string());
        let string_length = FunctionCategory::arrow(|s: String| s.len());

        let composed = FunctionCategory::compose_morphisms(&string_length, &int_to_string);

        assert_eq!(composed(42), 2); // "42".len() = 2
        assert_eq!(composed(123), 3); // "123".len() = 3
        assert_eq!(composed(-456), 4); // "-456".len() = 4
    }
}

/// Test Arrow trait implementation
#[cfg(test)]
mod arrow_tests {
    use super::*;

    #[test]
    fn test_arrow_arrow() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let to_upper = FunctionCategory::arrow(|s: String| s.to_uppercase());

        assert_eq!(double(21), 42);
        assert_eq!(to_upper("hello".to_string()), "HELLO");
    }

    #[test]
    fn test_first_operation() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let first_double = FunctionCategory::first(&double);

        assert_eq!(first_double((5, "hello")), (10, "hello"));
        assert_eq!(first_double((0, "world")), (0, "world"));
        assert_eq!(first_double((-3, "test")), (-6, "test"));
    }

    #[test]
    fn test_second_operation() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let second_double = FunctionCategory::second(&double);

        assert_eq!(second_double(("hello", 5)), ("hello", 10));
        assert_eq!(second_double(("world", 0)), ("world", 0));
        assert_eq!(second_double(("test", -3)), ("test", -6));
    }

    #[test]
    fn test_split_operation() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let square = FunctionCategory::arrow(|x: i32| x * x);

        let split_both = FunctionCategory::split(&double, &square);

        assert_eq!(split_both(5), (10, 25)); // (5*2, 5*5)
        assert_eq!(split_both(3), (6, 9)); // (3*2, 3*3)
        assert_eq!(split_both(-2), (-4, 4)); // (-2*2, (-2)*(-2))
    }

    #[test]
    fn test_combine_morphisms() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let length = FunctionCategory::arrow(|s: String| s.len());

        let combine_both = FunctionCategory::combine_morphisms(&double, &length);

        assert_eq!(combine_both((5, "hello".to_string())), (10, 5));
        assert_eq!(combine_both((3, "test".to_string())), (6, 4));
        assert_eq!(combine_both((0, "".to_string())), (0, 0));
    }

    #[test]
    fn test_split_with_different_types() {
        let to_string = FunctionCategory::arrow(|x: i32| x.to_string());
        let is_even = FunctionCategory::arrow(|x: i32| x % 2 == 0);

        let mixed_split = FunctionCategory::split(&to_string, &is_even);

        assert_eq!(mixed_split(6), ("6".to_string(), true));
        assert_eq!(mixed_split(7), ("7".to_string(), false));
        assert_eq!(mixed_split(0), ("0".to_string(), true));
    }
}

/// Test convenience methods
#[cfg(test)]
mod convenience_tests {
    use super::*;

    #[test]
    fn test_both_method() {
        let double_both = FunctionCategory::both(|x: i32| x * 2);

        assert_eq!(double_both((3, 5)), (6, 10));
        assert_eq!(double_both((0, -1)), (0, -2));
        assert_eq!(double_both((-2, 4)), (-4, 8));
    }

    #[test]
    fn test_when_method() {
        let double_if_even = FunctionCategory::when(|x: &i32| *x % 2 == 0, |x: i32| x * 2);

        assert_eq!(double_if_even(4), 8); // Even, so doubled
        assert_eq!(double_if_even(3), 3); // Odd, so unchanged
        assert_eq!(double_if_even(0), 0); // Even, so doubled
        assert_eq!(double_if_even(-5), -5); // Odd, so unchanged
        assert_eq!(double_if_even(-6), -12); // Even, so doubled
    }
}

/// Test function macro
#[cfg(test)]
mod macro_tests {
    use super::*;

    #[test]
    fn test_function_macro() {
        function!(double: i32 => i32 = |x: i32| x * 2);
        function!(to_string: i32 => String = |x: i32| x.to_string());
        function!(is_positive: i32 => bool = |x: i32| x > 0);

        assert_eq!(double(21), 42);
        assert_eq!(to_string(42), "42");
        assert_eq!(is_positive(5), true);
        assert_eq!(is_positive(-3), false);
        assert_eq!(is_positive(0), false);
    }

    #[test]
    fn test_function_macro_composition() {
        function!(double: i32 => i32 = |x: i32| x * 2);
        function!(add_ten: i32 => i32 = |x: i32| x + 10);
        function!(to_string: i32 => String = |x: i32| x.to_string());

        let step1 = FunctionCategory::compose_morphisms(&add_ten, &double);
        let pipeline = FunctionCategory::compose_morphisms(&to_string, &step1);

        assert_eq!(pipeline(5), "20"); // (5*2)+10 = 20 -> "20"
        assert_eq!(pipeline(0), "10"); // (0*2)+10 = 10 -> "10"
        assert_eq!(pipeline(-2), "6"); // (-2*2)+10 = 6 -> "6"
    }
}

/// Test complex scenarios and edge cases
#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_complex_pipeline() {
        // Create a complex data processing pipeline
        let parse_abs = FunctionCategory::arrow(|x: i32| x.abs());
        let validate_range = FunctionCategory::when(|x: &i32| *x <= 100, |x: i32| x);
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let format_result = FunctionCategory::arrow(|x: i32| format!("Result: {}", x));

        // Compose the pipeline
        let step1 = FunctionCategory::compose_morphisms(&validate_range, &parse_abs);
        let step2 = FunctionCategory::compose_morphisms(&double, &step1);
        let pipeline = FunctionCategory::compose_morphisms(&format_result, &step2);

        assert_eq!(pipeline(-50), "Result: 100"); // abs(-50) = 50, 50 <= 100, 50*2 = 100
        assert_eq!(pipeline(25), "Result: 50"); // abs(25) = 25, 25 <= 100, 25*2 = 50
        assert_eq!(pipeline(150), "Result: 300"); // abs(150) = 150, 150 > 100 (unchanged), 150*2 = 300
    }

    #[test]
    fn test_parallel_processing() {
        // Test parallel processing with split
        function!(extract_length: String => usize = |s: String| s.len());
        function!(to_uppercase: String => String = |s: String| s.to_uppercase());
        function!(count_vowels: String => usize = |s: String| {
            s.chars().filter(|c| "aeiouAEIOU".contains(*c)).count()
        });

        let length_and_upper = FunctionCategory::split(&extract_length, &to_uppercase);
        let process_string = FunctionCategory::combine_morphisms(&length_and_upper, &count_vowels);

        let input = ("hello world".to_string(), "programming".to_string());
        let result = process_string(input);

        // ("hello world".len(), "hello world".to_uppercase(), "programming" vowel count)
        // (11, "HELLO WORLD", 3)
        assert_eq!(result, ((11, "HELLO WORLD".to_string()), 3));
    }

    #[test]
    fn test_nested_arrow_operations() {
        let double = FunctionCategory::arrow(|x: i32| x * 2);
        let add_one = FunctionCategory::arrow(|x: i32| x + 1);

        // Test nested first operations
        let first_double = FunctionCategory::first(&double);
        let first_first_double = FunctionCategory::first(&first_double);

        let input = ((5, "hello"), "world");
        let result = first_first_double(input);
        assert_eq!(result, ((10, "hello"), "world"));

        // Test combination of first and second
        let second_add_one = FunctionCategory::second(&add_one);
        let combined = FunctionCategory::combine_morphisms(&first_double, &second_add_one);

        let input2 = ((3, "test"), ("data", 7));
        let result2 = combined(input2);
        assert_eq!(result2, ((6, "test"), ("data", 8)));
    }

    #[test]
    fn test_memory_safety_with_arc() {
        // Test that Arc sharing works correctly
        let expensive_computation = FunctionCategory::arrow(|x: i32| {
            // Simulate expensive computation
            std::thread::sleep(std::time::Duration::from_millis(1));
            x * x * x
        });

        // Create multiple references to the same morphism
        let ref1 = expensive_computation.clone();
        let ref2 = expensive_computation.clone();

        // All should produce the same results
        assert_eq!(expensive_computation(3), 27);
        assert_eq!(ref1(3), 27);
        assert_eq!(ref2(3), 27);

        // Test composition with shared references
        let composed = FunctionCategory::compose_morphisms(&ref1, &ref2);
        assert_eq!(composed(2), 512); // (2^3)^3 = 8^3 = 512
    }

    #[test]
    fn test_error_handling_patterns() {
        // Test safe division with Option
        let safe_divide =
            FunctionCategory::arrow(|x: i32| if x != 0 { Some(100 / x) } else { None });

        let handle_option = FunctionCategory::arrow(|opt: Option<i32>| opt.unwrap_or(0));

        let safe_division_pipeline =
            FunctionCategory::compose_morphisms(&handle_option, &safe_divide);

        assert_eq!(safe_division_pipeline(5), 20); // 100/5 = 20
        assert_eq!(safe_division_pipeline(0), 0); // None -> 0
        assert_eq!(safe_division_pipeline(-4), -25); // 100/(-4) = -25
    }
}

/// Performance and stress tests
#[cfg(test)]
mod performance_tests {
    use super::*;

    #[test]
    fn test_deep_composition() {
        // Test composition of many functions
        let add_one = FunctionCategory::arrow(|x: i32| x + 1);

        let mut composed = add_one.clone();
        for _ in 0..100 {
            composed = FunctionCategory::compose_morphisms(&composed, &add_one);
        }

        // Should add 101 total (original + 100 compositions)
        assert_eq!(composed(0), 101);
        assert_eq!(composed(10), 111);
    }

    #[test]
    fn test_large_data_processing() {
        let process_vec = FunctionCategory::arrow(|v: Vec<i32>| {
            v.into_iter()
                .map(|x| x * 2)
                .filter(|x| *x > 0)
                .collect::<Vec<_>>()
        });

        let sum_vec = FunctionCategory::arrow(|v: Vec<i32>| v.into_iter().sum::<i32>());

        let pipeline = FunctionCategory::compose_morphisms(&sum_vec, &process_vec);

        let large_input: Vec<i32> = (-1000..1000).collect();
        let result = pipeline(large_input);

        // Sum of positive even numbers from 2 to 1998
        let expected: i32 = (1..1000).map(|x| x * 2).sum();
        assert_eq!(result, expected);
    }
}
