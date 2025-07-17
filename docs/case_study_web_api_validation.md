# Case Study: Real-World Web API Error Handling with Validated

This guide demonstrates a practical, real-world use case for Rustica: validating incoming data from a web API and providing a clean, user-friendly error response. We'll build a simple user registration endpoint that validates multiple fields and accumulates all errors, rather than failing on the first one.

This is a common requirement in web development, and it's where the `Validated` data type and the Applicative Functor pattern truly shine.

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

    username_v
        .lift2(&email_v, |username, email| {
            (username.clone(), email.clone()) // Intermediate tuple
        })
        .lift2(&password_v, |(username, email), password| {
            UserRegistration {
                username: username.to_string(), // Cloned in the previous step
                email: email.to_string(),       // Cloned in the previous step
                password: password.clone(),
            }
        })
}

fn main() {
    // --- Case 1: All valid input ---
    let valid_input = UserRegistration {
        username: "alice_in_wonderland".to_string(),
        email: "alice@example.com".to_string(),
        password: "a_very_secure_password".to_string(),
    };

    let result = validate_registration(&valid_input);
    assert!(matches!(result, Validated::Valid(_)));
    println!("Validation succeeded for: {:?}", result.unwrap());

    // --- Case 2: All invalid input ---
    let invalid_input = UserRegistration {
        username: "al".to_string(),
        email: "alice.com".to_string(), // Missing '@'
        password: "123".to_string(),
    };

    let result = validate_registration(&invalid_input);
    match result {
        Validated::Invalid(errors) => {
            println!("Validation failed with {} errors:", errors.len());
            // Note: The order of errors is not guaranteed
            for err in errors {
                println!("- {:?}", err);
            }
        }
        _ => panic!("Expected validation to fail!"),
    }
    // Expected Output (order may vary):
    // Validation failed with 3 errors:
    // - UsernameTooShort
    // - InvalidEmailFormat
    // - PasswordTooWeak
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

fn main() {
    // --- Test the handler with invalid data ---
    let invalid_input = UserRegistration {
        username: "al".to_string(),
        email: "alice.com".to_string(),
        password: "123".to_string(),
    };

    let response = handle_registration_request(&invalid_input);
    println!("API Response for invalid data: {:?}", response);

    assert!(matches!(response, ApiResponse::Error { errors: _ }));

    // --- Test the handler with valid data ---
    let valid_input = UserRegistration {
        username: "alice_in_wonderland".to_string(),
        email: "alice@example.com".to_string(),
        password: "a_very_secure_password".to_string(),
    };

    let response = handle_registration_request(&valid_input);
    println!("API Response for valid data: {:?}", response);

    assert!(matches!(response, ApiResponse::Success { username: _ }));
}
```

This completes the loop. We've taken raw input, validated it in a functional and composable way, and produced a clean, structured response that is perfect for a modern web API.

## Conclusion

This case study demonstrates how Rustica's `Validated` data type and the Applicative Functor pattern provide a robust and elegant solution for a common real-world problem. By using these tools, you can write validation logic that is:

- **Composable**: Small, reusable validation functions can be combined to build complex rules.
- **Declarative**: The validation logic is clear and easy to read, without nested `if/else` statements.
- **User-Friendly**: It can accumulate all errors, providing better feedback to the user.
- **Robust**: The type system ensures you handle both success and failure cases.
