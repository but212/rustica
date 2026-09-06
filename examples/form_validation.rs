//! User Registration & Validation Example
//!
//! Demonstrates error accumulation with `Validated`, immutable history
//! tracking with `PersistentVector`, and functional composition.

use rustica::datatypes::validated::Validated;
use rustica::pvec::{PersistentVector, pvec};
use rustica::traits::applicative::Applicative;

#[derive(Debug, Clone, PartialEq)]
pub struct User {
    pub username: String,
    pub email: String,
    pub age: u32,
}

fn validate_username(username: &str) -> Validated<String, String> {
    if username.trim().len() >= 3 {
        Validated::valid(username.trim().to_string())
    } else {
        Validated::invalid("Username must be at least 3 characters long".to_string())
    }
}

fn validate_email(email: &str) -> Validated<String, String> {
    if email.contains('@') && email.contains('.') {
        Validated::valid(email.trim().to_string())
    } else {
        Validated::invalid("Email must contain '@' and a domain".to_string())
    }
}

fn validate_age(age: u32) -> Validated<String, u32> {
    if age >= 18 {
        Validated::valid(age)
    } else {
        Validated::invalid("User must be at least 18 years old".to_string())
    }
}

fn validate_user(username: &str, email: &str, age: u32) -> Validated<String, User> {
    let u = validate_username(username);
    let e = validate_email(email);
    let a = validate_age(age);

    // Combine username and email first
    let user_base = Validated::<String, (String, String)>::lift2(|u, e| (u, e), u, e);

    // Combine with age to construct User
    Validated::<String, User>::lift2(
        |(u, e), a| User {
            username: u,
            email: e,
            age: a,
        },
        user_base,
        a,
    )
}

fn main() {
    println!("=== Rustica Form Validation Example ===\n");

    // Case 1: Multiple Validation Failures (Error Accumulation)
    println!("1. Validating invalid input (fails multiple checks):");
    let invalid_result = validate_user("a", "invalid-email", 15);
    match invalid_result {
        Validated::Valid(user) => println!("Success: {:?}", user),
        Validated::Invalid(errors) => {
            println!("Validation failed with {} error(s):", errors.len());
            for (idx, err) in errors.iter().enumerate() {
                println!("  [{}] {}", idx + 1, err);
            }
        },
    }

    println!();

    // Case 2: Successful Validation
    println!("2. Validating valid input:");
    let valid_result = validate_user("ferris", "ferris@rust-lang.org", 24);
    match &valid_result {
        Validated::Valid(user) => println!("Registered user successfully: {:?}", user),
        Validated::Invalid(errors) => println!("Failed: {:?}", errors),
    }

    println!();

    // Case 3: Persistent Immutable History with PersistentVector
    println!("3. Storing users in PersistentVector (immutable history):");
    let mut history: PersistentVector<User> = pvec![];

    if let Validated::Valid(user1) = valid_result {
        history = history.push_back(user1);
    }

    let second_valid = validate_user("corro", "corro@example.com", 30);
    if let Validated::Valid(user2) = second_valid {
        let history_v2 = history.push_back(user2);

        println!("  Initial history count: {}", history.len());
        println!("  Updated history count: {}", history_v2.len());
        for (i, u) in history_v2.iter().enumerate() {
            println!("  User #{}: {} ({})", i + 1, u.username, u.email);
        }
    }
}
