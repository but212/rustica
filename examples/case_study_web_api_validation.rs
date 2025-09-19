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

/// Takes the raw input and runs all validations.
fn validate_registration(input: &UserRegistration) -> Validated<ValidationError, UserRegistration> {
    let username_v = validate_username(&input.username);
    let email_v = validate_email(&input.email);
    let password_v = validate_password(&input.password);

    Validated::lift3(
        |username, email, password| UserRegistration {
            username,
            email,
            password,
        },
        &username_v,
        &email_v,
        &password_v,
    )
}

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
                assert!(
                    errors.contains(&"Username must be at least 3 characters long.".to_string())
                );
                assert!(errors.contains(&"Email is not in a valid format.".to_string()));
                assert!(
                    errors.contains(&"Password must be at least 8 characters long.".to_string())
                );
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
                assert!(
                    errors.contains(&"Password must be at least 8 characters long.".to_string())
                );
            },
            _ => panic!("Expected error response"),
        }
    }
}

fn main() {
    println!("Web API Validation Case Study");
    println!("This example demonstrates how to use Rustica's functional programming constructs");
    println!("to build a robust validation system for a web API.");
    println!();
    println!("Key Features Demonstrated:");
    println!("- Validated Type: Using Validated<E, A> for accumulating validation errors");
    println!("- Composable Validation: Individual validation functions that can be combined");
    println!(
        "- Functional Error Handling: Clean separation of validation logic and error presentation"
    );
    println!("- Type Safety: Compile-time guarantees about validation states");

    println!();
    println!("Running validation examples...");

    // Run some example validations
    let valid_input = UserRegistration {
        username: "alice".to_string(),
        email: "alice@example.com".to_string(),
        password: "securepassword123".to_string(),
    };

    let invalid_input = UserRegistration {
        username: "alice".to_string(),
        email: "invalid-email".to_string(),
        password: "short".to_string(),
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
