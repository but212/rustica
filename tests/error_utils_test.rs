use rustica::utils::error_utils::*;
use rustica::datatypes::either::Either;
use rustica::datatypes::validated::Validated;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
struct TestError(&'static str);

impl fmt::Display for TestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TestError: {}", self.0)
    }
}

#[test]
fn test_sequence() {
    // Test with all Ok values
    let ok_values: Vec<Result<i32, TestError>> = vec![Ok(1), Ok(2), Ok(3)];
    let result = sequence(ok_values);
    assert_eq!(result, Ok(vec![1, 2, 3]));

    // Test with some Err values
    let mixed_values: Vec<Result<i32, TestError>> = vec![
        Ok(1),
        Err(TestError("error")),
        Ok(3),
    ];
    let result = sequence(mixed_values);
    assert_eq!(result, Err(TestError("error")));
}

#[test]
fn test_traverse() {
    // Test with a function that always succeeds
    let values = vec![1, 2, 3];
    let result = traverse(values, |x| Ok::<_, TestError>(x * 2));
    assert_eq!(result, Ok(vec![2, 4, 6]));

    // Test with a function that sometimes fails
    let values = vec![1, 0, 3];
    let result = traverse(values, |x| {
        if x == 0 {
            Err(TestError("division by zero"))
        } else {
            Ok(10 / x)
        }
    });
    assert_eq!(result, Err(TestError("division by zero")));
}

#[test]
fn test_traverse_validated() {
    // Test with all successful values
    let values = vec![1, 2, 3];
    let result = traverse_validated(values, |x| Ok::<_, TestError>(x * 2));
    assert_eq!(result, Validated::valid(vec![2, 4, 6]));

    // Test with some errors
    let values = vec![1, 0, 3, 0, 5];
    let result = traverse_validated(values, |x| {
        if x == 0 {
            Err(TestError("division by zero"))
        } else {
            Ok(10 / x)
        }
    });
    
    assert!(result.is_invalid());
    let errors = result.errors();
    assert_eq!(errors.len(), 2);
    assert!(errors.contains(&TestError("division by zero")));
}

#[test]
fn test_result_extensions() {
    // Test to_validated extension
    let ok_result: Result<i32, TestError> = Ok(42);
    let err_result: Result<i32, TestError> = Err(TestError("error"));
    
    assert_eq!(ok_result.clone().to_validated(), Validated::valid(42));
    assert_eq!(err_result.clone().to_validated(), Validated::invalid(TestError("error")));
    
    // Test to_either extension
    assert_eq!(ok_result.clone().to_either(), Either::right(42));
    assert_eq!(err_result.clone().to_either(), Either::left(TestError("error")));
    
    // Test bimap extension
    let transformed = ok_result.bimap(|x| x.to_string(), |e| format!("Error: {:?}", e));
    assert_eq!(transformed, Ok("42".to_string()));
    
    let transformed = err_result.bimap(|x| x.to_string(), |e| format!("Error: {:?}", e));
    assert_eq!(transformed, Err("Error: TestError(\"error\")".to_string()));
}

#[test]
fn test_with_error_trait() {
    // Test WithError implementation for Result
    let ok_result: Result<i32, TestError> = Ok(42);
    let err_result: Result<i32, TestError> = Err(TestError("error"));
    
    assert_eq!(ok_result.clone().to_result(), Ok(42));
    assert_eq!(err_result.clone().to_result(), Err(TestError("error")));
    
    // Test WithError implementation for Either
    let right: Either<TestError, i32> = Either::right(42);
    let left: Either<TestError, i32> = Either::left(TestError("error"));
    
    assert_eq!(right.clone().to_result(), Ok(42));
    assert_eq!(left.clone().to_result(), Err(TestError("error")));
    
    // Test WithError implementation for Validated
    let valid: Validated<TestError, i32> = Validated::valid(42);
    let invalid: Validated<TestError, i32> = Validated::invalid(TestError("error"));
    
    assert_eq!(valid.clone().to_result(), Ok(42));
    assert_eq!(invalid.clone().to_result(), Err(TestError("error")));
    
    // Test sequence_with_error function with different types
    let eithers = vec![
        Either::<TestError, i32>::right(1),
        Either::right(2),
        Either::right(3),
    ];
    assert_eq!(sequence_with_error(eithers), Ok(vec![1, 2, 3]));
    
    let eithers = vec![
        Either::<TestError, i32>::right(1),
        Either::left(TestError("error")),
        Either::right(3),
    ];
    assert_eq!(sequence_with_error(eithers), Err(TestError("error")));
}

#[test]
fn test_custom_error() {
    // Test creating errors with context
    let simple_error = error("File not found");
    assert_eq!(simple_error.message(), &"File not found");
    assert_eq!(simple_error.context(), None::<&()>);
    
    let contextualized = error_with_context("Network error", "while connecting to api.example.com");
    assert_eq!(contextualized.message(), &"Network error");
    assert_eq!(contextualized.context(), Some(&"while connecting to api.example.com"));
    
    // Test error mapping
    let mapped = contextualized.map(|msg| format!("ERROR: {}", msg));
    assert_eq!(mapped.message(), &"ERROR: Network error");
    assert_eq!(mapped.context(), Some(&"while connecting to api.example.com"));
}

#[test]
fn test_conversion_functions() {
    // Test result_to_either
    let ok_result: Result<i32, &str> = Ok(42);
    let err_result: Result<i32, &str> = Err("error");
    
    assert_eq!(result_to_either(ok_result), Either::right(42));
    assert_eq!(result_to_either(err_result), Either::left("error"));
    
    // Test either_to_result
    let right: Either<&str, i32> = Either::right(42);
    let left: Either<&str, i32> = Either::left("error");
    
    assert_eq!(either_to_result(right), Ok(42));
    assert_eq!(either_to_result(left), Err("error"));
}
