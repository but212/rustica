//! Example demonstrating the standardized error handling utilities
//!
//! This example shows how to use the error handling utilities from the `error_utils` module
//! to standardize error handling across an application.

use rustica::utils::error_utils::{
    self, error_with_context, sequence, traverse, traverse_validated, ResultExt, WithError,
};
use rustica::datatypes::either::Either;
use rustica::datatypes::validated::Validated;
use std::fmt::Debug;

// A domain-specific error type
#[derive(Debug, Clone)]
enum AppError {
    ParseError(String),
    ValidationError(String),
    NetworkError { url: String, message: String },
}

// A domain-specific result type
type AppResult<T> = Result<T, AppError>;

// Simulated functions that can fail
fn parse_number(input: &str) -> AppResult<i32> {
    input
        .parse::<i32>()
        .map_err(|e| AppError::ParseError(format!("Failed to parse '{}': {}", input, e)))
}

fn validate_positive(value: i32) -> AppResult<i32> {
    if value > 0 {
        Ok(value)
    } else {
        Err(AppError::ValidationError(format!(
            "Expected positive value, got {}",
            value
        )))
    }
}

fn fetch_data(url: &str) -> AppResult<String> {
    // Simulate a network request
    if url.starts_with("https://") {
        Ok(format!("Data from {}", url))
    } else {
        Err(AppError::NetworkError {
            url: url.to_string(),
            message: "Invalid URL scheme".to_string(),
        })
    }
}

// Using the error handling utilities
fn process_inputs(inputs: &[&str]) -> AppResult<Vec<i32>> {
    // Use traverse to apply a function that can fail to each input
    traverse(inputs, |input| {
        // Chain operations with ?
        let num = parse_number(input)?;
        validate_positive(num)
    })
}

fn process_inputs_collect_all_errors(inputs: &[&str]) -> Validated<AppError, Vec<i32>> {
    // Use traverse_validated to collect all errors
    traverse_validated(inputs, |input| {
        let num = parse_number(input)?;
        validate_positive(num)
    })
}

fn process_urls(urls: &[&str]) -> AppResult<Vec<String>> {
    // First map each URL to a Result
    let results: Vec<AppResult<String>> = urls.iter().map(|url| fetch_data(url)).collect();
    
    // Then use sequence to combine the Results
    sequence(results)
}

fn convert_error_types<T, E: Debug>(result: Result<T, E>) -> Either<String, T> {
    // Use the ResultExt trait to convert between error types
    result.map_err(|e| format!("Error: {:?}", e)).to_either()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Error Handling Example ===\n");

    // Example 1: Processing a list of valid inputs
    let valid_inputs = ["10", "20", "30"];
    match process_inputs(&valid_inputs) {
        Ok(values) => println!("Valid inputs processed successfully: {:?}", values),
        Err(e) => println!("Error processing valid inputs: {:?}", e),
    }

    // Example 2: Processing a list with some invalid inputs
    let mixed_inputs = ["10", "-5", "not a number", "30"];
    match process_inputs(&mixed_inputs) {
        Ok(values) => println!("Mixed inputs processed successfully: {:?}", values),
        Err(e) => println!("Error processing mixed inputs: {:?}", e),
    }

    // Example 3: Collecting all errors instead of stopping at the first one
    let mixed_inputs = ["10", "-5", "not a number", "30"];
    let validated_result = process_inputs_collect_all_errors(&mixed_inputs);
    match validated_result {
        Validated::Valid(values) => println!("All inputs valid: {:?}", values),
        _ => {
            println!("Some inputs invalid. Errors:");
            for error in validated_result.errors() {
                println!("  - {:?}", error);
            }
        }
    }

    // Example 4: Processing URLs with sequence
    let urls = ["https://example.com", "http://invalid.com"];
    match process_urls(&urls) {
        Ok(data) => println!("URL data: {:?}", data),
        Err(e) => println!("Error fetching URLs: {:?}", e),
    }

    // Example 5: Converting between error types
    let result: Result<i32, &str> = Err("Something went wrong");
    let either = convert_error_types(result);
    println!("Converted error: {:?}", either);

    // Example 6: Using custom error types with context
    let app_error = error_with_context(
        "Connection timeout",
        "Trying to connect to database",
    );
    println!("Error with context: {}", app_error);

    // Example 7: Using the WithError trait for polymorphic error handling
    fn process_any_error_type<C, E>(collection: Vec<C>) -> Result<Vec<C::Success>, E>
    where
        C: WithError<E>,
        E: Debug,
        <C as WithError<E>>::Success: Debug,
    {
        let result = error_utils::sequence_with_error(collection);
        println!("Generic error processing result: {:?}", result);
        result
    }

    let eithers = vec![
        Either::<&str, i32>::right(1),
        Either::right(2),
        Either::left("error"),
    ];
    let _ = process_any_error_type(eithers);

    Ok(())
}
