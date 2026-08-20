use rustica::category::function_category::FunctionCategory;

#[test]
fn test_function_category_inherent_api_without_trait_imports() {
    let id = FunctionCategory::identity_morphism::<i32>();
    assert_eq!(id(42), 42);

    let double = FunctionCategory::arrow(|x: i32| x * 2);
    let add_one = FunctionCategory::arrow(|x: i32| x + 1);

    // compose_morphisms(g, f) computes g(f(x))
    let double_then_add = FunctionCategory::compose_morphisms(&add_one, &double);
    assert_eq!(double_then_add(5), 11);

    let add_then_double = FunctionCategory::compose_morphisms(&double, &add_one);
    assert_eq!(add_then_double(5), 12);

    let first_f = FunctionCategory::first(&double);
    assert_eq!(first_f((10, "keep".to_string())), (20, "keep".to_string()));

    let second_f = FunctionCategory::second(&double);
    assert_eq!(second_f(("keep".to_string(), 10)), ("keep".to_string(), 20));

    let square = FunctionCategory::arrow(|x: i32| x * x);
    let split_f = FunctionCategory::split(&double, &square);
    assert_eq!(split_f(4), (8, 16));

    let to_str = FunctionCategory::arrow(|x: i32| x.to_string());
    let combine_f = FunctionCategory::combine_morphisms(&double, &to_str);
    assert_eq!(combine_f((5, 10)), (10, "10".to_string()));
}
