// Import necessary traits to bring their methods into scope
use rustica::traits::monad_error::{ErrorMapper, MonadError};

#[test]
fn test_result_throw() {
    // Explicitly annotate types for clarity in generic contexts
    let thrown: Result<i32, String> = Result::<i32, String>::throw("error".to_string());
    assert!(thrown.is_err());
    assert_eq!(thrown.unwrap_err(), "error".to_string());
}

#[test]
fn test_result_catch() {
    // Test catching an error with reference-based method
    let error_result: Result<i32, String> = Err("not found".to_string());
    let handled = error_result.catch(|e| {
        if e == "not found" {
            Ok(0)
        } else {
            Err(e.clone())
        }
    });
    assert_eq!(handled, Ok(0));

    // Test not catching a success value
    let success: Result<i32, String> = Ok(42);
    let still_success = success.catch(|_| Ok(0));
    assert_eq!(still_success, Ok(42));
}

#[test]
fn test_result_catch_owned() {
    // Test catching an error with ownership-based method
    let error_result: Result<i32, String> = Err("not found".to_string());
    let handled = error_result.catch_owned(|e| if e == "not found" { Ok(0) } else { Err(e) });
    assert_eq!(handled, Ok(0));

    // Test not catching a success value
    let success: Result<i32, String> = Ok(42);
    let still_success = success.catch_owned(|_| Ok(0));
    assert_eq!(still_success, Ok(42));
}

#[test]
fn test_result_map_error() {
    // Test mapping error type with reference-based method
    let error_result: Result<i32, String> = Err("not found".to_string());
    let mapped = error_result.map_error_to(|e| format!("Error: {e}"));
    assert_eq!(mapped, Err("Error: not found".to_string()));

    // Test not mapping a success value's error
    let success: Result<i32, String> = Ok(42);
    let still_success = success.map_error_to(|e| e.to_string());
    assert_eq!(still_success, Ok(42));
}

#[test]
fn test_result_map_error_owned() {
    // Test mapping error type with ownership-based method
    let error_result: Result<i32, String> = Err("not found".to_string());
    let mapped = error_result.map_error_to_owned(|e| format!("Error: {e}"));
    assert_eq!(mapped, Err("Error: not found".to_string()));

    // Test not mapping a success value's error
    let success: Result<i32, String> = Ok(42);
    let still_success = success.map_error_to_owned(|e| e.to_string());
    assert_eq!(still_success, Ok(42));
}

#[test]
fn test_option_throw() {
    let thrown: Option<i32> = Option::<i32>::throw(());
    assert_eq!(thrown, None);
}

#[test]
fn test_option_catch() {
    // Test catching an error (None) with reference-based method
    let none_value: Option<i32> = None;
    let handled = none_value.catch(|_| Some(0));
    assert_eq!(handled, Some(0));

    // Test not catching a success value
    let some_value: Option<i32> = Some(42);
    let still_some = some_value.catch(|_| Some(0));
    assert_eq!(still_some, Some(42));
}

#[test]
fn test_option_catch_owned() {
    // Test catching an error (None) with ownership-based method
    let none_value: Option<i32> = None;
    let handled = none_value.catch_owned(|_| Some(0));
    assert_eq!(handled, Some(0));

    // Test not catching a success value
    let some_value: Option<i32> = Some(42);
    let still_some = some_value.catch_owned(|_| Some(0));
    assert_eq!(still_some, Some(42));
}

#[test]
fn test_option_map_error() {
    // Test mapping error type with reference-based method
    let none_value: Option<i32> = None;
    let mapped = none_value.map_error_to(|_| "Not found".to_string());
    assert_eq!(mapped, Err("Not found".to_string()));

    // Test not mapping a success value's error
    let some_value: Option<i32> = Some(42);
    let still_some = some_value.map_error_to(|_| "Not found".to_string());
    assert_eq!(still_some, Ok(42));
}

#[test]
fn test_option_map_error_owned() {
    // Test mapping error type with ownership-based method
    let none_value: Option<i32> = None;
    let mapped = none_value.map_error_to_owned(|_| "Not found".to_string());
    assert_eq!(mapped, Err("Not found".to_string()));

    // Test not mapping a success value's error
    let some_value: Option<i32> = Some(42);
    let still_some = some_value.map_error_to_owned(|_| "Not found".to_string());
    assert_eq!(still_some, Ok(42));
}

#[test]
fn test_monad_error_laws() {
    // 1. Left Catch Law: throw(e).catch(h) == h(e)
    let error = "test error".to_string();
    let thrown: Result<i32, String> = Result::<i32, String>::throw(error.clone());
    let handler = |e: &String| {
        if e == "test error" {
            Ok(42)
        } else {
            Err(e.clone())
        }
    };
    let caught = thrown.catch(handler);
    let direct = handler(&error);
    assert_eq!(caught, direct);

    // 2. Right Catch Law: m.catch(throw) == m
    let m: Result<i32, String> = Ok(10);
    let caught_m = m.catch(|e| Result::<i32, String>::throw(e.clone()));
    assert_eq!(caught_m, m);
}

#[test]
fn test_error_mapper_conversion() {
    // Test converting between error types
    let result: Result<i32, String> = Err("Not found".to_string());

    // Convert to a different error type
    let with_code = result.map_error_to(|e| (404, e.clone()));
    assert_eq!(with_code, Err((404, "Not found".to_string())));

    // Chain error mappings
    let as_string = with_code.map_error_to(|(code, msg)| format!("Error {code}: {msg}"));
    assert_eq!(as_string, Err("Error 404: Not found".to_string()));
}

#[test]
fn test_io_error_handling() {
    // More realistic example using a custom error that can handle IO errors
    #[derive(Debug, Clone)]
    struct AppError {
        message: String,
        kind: String,
    }

    let error = AppError {
        message: "File not found".to_string(),
        kind: "NotFound".to_string(),
    };

    let result: Result<String, AppError> = Err(error);

    // Transform to a different error type
    let string_error = result.map_error_to(|e| format!("{}: {}", e.kind, e.message));
    assert!(string_error.is_err());
    assert_eq!(string_error.unwrap_err(), "NotFound: File not found");

    // Test the full chain: throw -> catch -> map_error
    let thrown: Result<i32, AppError> = Result::<i32, AppError>::throw(AppError {
        message: "Invalid input".to_string(),
        kind: "InvalidArgument".to_string(),
    });

    let caught = thrown.catch(|e| {
        if e.kind == "NotFound" {
            // Provide default for not found errors
            Ok(0)
        } else {
            // Pass through other errors
            Err(e.clone())
        }
    });

    let handled = caught.map_error_to(|e| format!("Error: {}", e.message));

    assert_eq!(handled, Err("Error: Invalid input".to_string()));
}
