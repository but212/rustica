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

    let intermediate = Validated::<ValidationError, (String, String)>::lift2(
        |username, email| {
            (username.clone(), email.clone()) // Intermediate tuple
        },
        &username_v,
        &email_v,
    );
    
    Validated::<ValidationError, UserRegistration>::lift2(
        |(username, email), password| {
            UserRegistration {
                username: username.to_string(), // Cloned in the previous step
                email: email.to_string(),       // Cloned in the previous step
                password: password.clone(),
            }
        },
        &intermediate,
        &password_v,
    )
}

#[test]
fn accumulating_errors_with_applicative_functors() {
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
        },
        _ => panic!("Expected validation to fail!"),
    }
    // Expected Output (order may vary):
    // Validation failed with 3 errors:
    // - UsernameTooShort
    // - InvalidEmailFormat
    // - PasswordTooWeak
}

#[test]
fn generating_the_api_response() {
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
