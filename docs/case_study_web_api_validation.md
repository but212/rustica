# Case Study: Real-World Web API Error Handling with Validated

This guide demonstrates a practical, real-world use case for Rustica: validating incoming data from a web API and providing a clean, user-friendly error response. We'll build a simple user registration endpoint that validates multiple fields and accumulates all errors, rather than failing on the first one.

This is a common requirement in web development, and it's where the `Validated` data type and the Applicative Functor pattern truly shine.

## Running the Example

You can run the interactive example to see the validation in action:

```bash
cargo run --example case_study_web_api_validation
```

The example demonstrates:

- **Interactive demonstration** with valid and invalid inputs
- **Comprehensive test suite** showing different validation scenarios
- **Real-world API response structure** with user-friendly error messages

## The Goal

We want to validate a request body for a user registration endpoint. The request might look like this:

```json
{
  "username": "al",
  "email": "alice@example",
  "password": "123"
}
```

Our goal is to validate all fields and, if there are errors, return a response that lists all of them, like this:

```json
{
  "errors": [
    "Username must be at least 3 characters long.",
    "Email is not in a valid format.",
    "Password must be at least 8 characters long."
  ]
}
```

If the data is valid, we'll return a success response.

Let's get started.

## 1. The Data Model and Validation Functions

First, let's define the data structure we're validating and the validation functions for each field. We'll also need a simple `Error` enum to represent our validation errors.

```rust
use rustica::prelude::*;

// Our simple error type
#[derive(Debug, Clone, PartialEq)]
pub enum ValidationError {
    UsernameTooShort,
    InvalidEmailFormat,
    PasswordTooWeak,
}

// The data we receive from the API
#[derive(Debug, Clone)]
pub struct UserRegistration {
    pub username: String,
    pub email: String,
    pub password: String,
}

// --- Individual Validation Functions ---

/// Validates that the username is at least 3 characters long.
fn validate_username(username: &str) -> Validated<ValidationError, String> {
    if username.len() < 3 {
        Validated::invalid(ValidationError::UsernameTooShort)
    } else {
        Validated::valid(username.to_string())
    }
}

/// Validates that the email contains an '@' symbol.
/// (This is a simplistic check for demonstration purposes.)
fn validate_email(email: &str) -> Validated<ValidationError, String> {
    if !email.contains('@') {
        Validated::invalid(ValidationError::InvalidEmailFormat)
    } else {
        Validated::valid(email.to_string())
    }
}

/// Validates that the password is at least 8 characters long.
fn validate_password(password: &str) -> Validated<ValidationError, String> {
    if password.len() < 8 {
        Validated::invalid(ValidationError::PasswordTooWeak)
    } else {
        Validated::valid(password.to_string())
    }
}
```

Each function is small, focused, and easy to test. They all return a `Validated` type, which is the key to accumulating errors.

## 2. Accumulating Errors with Applicative Functors

Now, let's create a function that validates a whole `UserRegistration` object. We'll use the `apply` method, which is the core of the Applicative pattern. When used with `Validated`, `apply` will collect all the `Invalid` results together.

To do this, we start with a `Validated` that contains a function (in this case, a curried constructor for `UserRegistration`) and then successively `apply` the results of our validation functions to it.

```rust
/// Takes the raw input and runs all validations.
fn validate_registration(input: &UserRegistration) -> Validated<ValidationError, UserRegistration> {
    let username_v = validate_username(&input.username);
    let email_v = validate_email(&input.email);
    let password_v = validate_password(&input.password);

    Validated::<ValidationError, UserRegistration>::lift3(
        |username, email, password| UserRegistration {
            username: username.clone(),
            email: email.clone(),
            password: password.clone(),
        },
        &username_v,
        &email_v,
        &password_v,
    )
}
```

As you can see, `validate_registration` is declarative. It lists the validations to be applied without any complex conditional logic. The `Validated` type handles all the machinery of collecting the errors for us.

## 3. Generating the API Response

Finally, let's see how this would fit into a web framework handler. The handler would receive the raw input, run our `validate_registration` function, and then map the `Valid` or `Invalid` cases to the appropriate HTTP response.

Here's a conceptual example. We'll use a simple `ApiResponse` enum to represent the JSON response.

```rust
// A simplified representation of our JSON API response
#[derive(Debug, PartialEq)]
enum ApiResponse {
    Success { username: String },
    Error { errors: Vec<String> },
}

// A mock API handler function
fn handle_registration_request(input: &UserRegistration) -> ApiResponse {
    match validate_registration(input) {
        Validated::Valid(valid_user) => ApiResponse::Success {
            username: valid_user.username,
        },
        Validated::Invalid(validation_errors) => {
            // Convert our ValidationError enum into user-friendly strings
            let error_messages = validation_errors
                .iter()
                .map(|e| match e {
                    ValidationError::UsernameTooShort => {
                        "Username must be at least 3 characters long.".to_string()
                    },
                    ValidationError::InvalidEmailFormat => {
                        "Email is not in a valid format.".to_string()
                    },
                    ValidationError::PasswordTooWeak => {
                        "Password must be at least 8 characters long.".to_string()
                    },
                })
                .collect();

            ApiResponse::Error {
                errors: error_messages,
            }
        },
    }
}
```

This completes the loop. We've taken raw input, validated it in a functional and composable way, and produced a clean, structured response that is perfect for a modern web API.

## 4. Interactive Example

The example includes a `main()` function that demonstrates the validation system in action:

```rust
fn main() {
    println!("Web API Validation Case Study");
    println!("This example demonstrates how to use Rustica's functional programming constructs");
    println!("to build a robust validation system for a web API.");
    println!();
    println!("Key Features Demonstrated:");
    println!("- Validated Type: Using Validated<E, A> for accumulating validation errors");
    println!("- Composable Validation: Individual validation functions that can be combined");
    println!("- Functional Error Handling: Clean separation of validation logic and error presentation");
    println!("- Type Safety: Compile-time guarantees about validation states");

    println!();
    println!("Running validation examples...");
    
    // Test with valid input
    let valid_input = UserRegistration {
        username: "alice".to_string(),
        email: "alice@example.com".to_string(),
        password: "securepassword123".to_string(),
    };

    println!("\nValidating valid input:");
    match handle_registration_request(&valid_input) {
        ApiResponse::Success { username } => {
            println!("✓ Registration successful for user: {}", username);
        },
        ApiResponse::Error { errors } => {
            println!("✗ Validation failed: {:?}", errors);
        },
    }

    // Test with invalid input
    let invalid_input = UserRegistration {
        username: "alice".to_string(),
        email: "invalid-email".to_string(),
        password: "short".to_string(),
    };

    println!("\nValidating invalid input:");
    match handle_registration_request(&invalid_input) {
        ApiResponse::Success { username } => {
            println!("✓ Registration successful for user: {}", username);
        },
        ApiResponse::Error { errors } => {
            println!("✗ Validation failed with {} errors:", errors.len());
            for error in errors {
                println!("  - {}", error);
            }
        },
    }
}
```

### Expected Output

When you run the example, you'll see output like this:

```text
Web API Validation Case Study
This example demonstrates how to use Rustica's functional programming constructs
to build a robust validation system for a web API.

Key Features Demonstrated:
- Validated Type: Using Validated<E, A> for accumulating validation errors
- Composable Validation: Individual validation functions that can be combined
- Functional Error Handling: Clean separation of validation logic and error presentation
- Type Safety: Compile-time guarantees about validation states

Running validation examples...

Validating valid input:
✓ Registration successful for user: alice

Validating invalid input:
✗ Validation failed with 2 errors:
  - Email is not in a valid format.
  - Password must be at least 8 characters long.
```

## 5. Testing

The example includes comprehensive tests that demonstrate different validation scenarios:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_registration() {
        let input = UserRegistration {
            username: "alice".to_string(),
            email: "alice@example.com".to_string(),
            password: "strongpassword".to_string(),
        };

        let response = handle_registration_request(&input);
        assert_eq!(
            response,
            ApiResponse::Success {
                username: "alice".to_string()
            }
        );
    }

    #[test]
    fn test_invalid_registration_all_fields() {
        let input = UserRegistration {
            username: "al".to_string(),
            email: "invalid-email".to_string(),
            password: "123".to_string(),
        };

        let response = handle_registration_request(&input);
        match response {
            ApiResponse::Error { errors } => {
                assert_eq!(errors.len(), 3);
                assert!(errors.contains(&"Username must be at least 3 characters long.".to_string()));
                assert!(errors.contains(&"Email is not in a valid format.".to_string()));
                assert!(errors.contains(&"Password must be at least 8 characters long.".to_string()));
            },
            _ => panic!("Expected error response"),
        }
    }

    #[test]
    fn test_partial_validation_errors() {
        let input = UserRegistration {
            username: "alice".to_string(),
            email: "invalid-email".to_string(),
            password: "short".to_string(),
        };

        let response = handle_registration_request(&input);
        match response {
            ApiResponse::Error { errors } => {
                assert_eq!(errors.len(), 2);
                assert!(errors.contains(&"Email is not in a valid format.".to_string()));
                assert!(errors.contains(&"Password must be at least 8 characters long.".to_string()));
            },
            _ => panic!("Expected error response"),
        }
    }
}
```

Run the tests with:

```bash
cargo test --example case_study_web_api_validation
```

## Conclusion

This case study demonstrates how Rustica's `Validated` data type and the Applicative Functor pattern provide a robust and elegant solution for a common real-world problem. By using these tools, you can write validation logic that is:

- **Composable**: Small, reusable validation functions can be combined to build complex rules.
- **Declarative**: The validation logic is clear and easy to read, without nested `if/else` statements.
- **User-Friendly**: It can accumulate all errors, providing better feedback to the user.
- **Robust**: The type system ensures you handle both success and failure cases.
- **Testable**: Each validation function can be tested independently, and the overall system has comprehensive test coverage.

### Key Features Demonstrated

- **Validated Type**: Using `Validated<E, A>` for accumulating validation errors
- **Composable Validation**: Individual validation functions that can be combined
- **Functional Error Handling**: Clean separation of validation logic and error presentation
- **Type Safety**: Compile-time guarantees about validation states
- **Interactive Examples**: Real-world demonstration with both valid and invalid inputs
- **Comprehensive Testing**: Full test coverage for different validation scenarios

This pattern is particularly useful in web APIs, form validation, configuration parsing, and any scenario where you need to collect and report multiple errors rather than failing fast on the first error encountered.
