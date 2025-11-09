//! Identity Trait Migration Guide for v0.11.0
//!
//! This example demonstrates how to migrate from the deprecated Identity trait
//! to standard Rust value extraction patterns and Comonad::extract().
//!
//! ## What's Deprecated in v0.11.0
//!
//! The Identity trait is deprecated and will be removed in v0.12.0:
//! - `Identity::value()` - Use `unwrap()` or `as_ref()` instead
//! - `Identity::try_value()` - Use `unwrap_or()` or proper error handling
//! - `Identity::into_value()` - Use `into_inner()` or standard conversion
//!
//! ## What's Retained
//!
//! - `unwrap()` - Standard value extraction for all types
//! - `unwrap_or()` - Safe default extraction
//! - `as_ref()` - Reference access without consuming
//! - `Comonad::extract()` - For types with guaranteed total extraction

use rustica::datatypes::choice::Choice;
use rustica::datatypes::either::Either;
use rustica::datatypes::id::Id;
use rustica::datatypes::maybe::Maybe;
use rustica::traits::comonad::Comonad;

fn main() {
    println!("Identity Trait Migration Examples for v0.11.0");
    println!("==============================================\n");

    demonstrate_option_migration();
    demonstrate_maybe_migration();
    demonstrate_choice_migration();
    demonstrate_either_migration();
    demonstrate_id_migration();
    demonstrate_comonad_usage();
    demonstrate_best_practices();
}

/// Demonstrate Option-like patterns (though Option doesn't implement Identity)
fn demonstrate_option_migration() {
    println!("1. Option-like Patterns (Standard Rust)");
    println!("---------------------------------------\n");

    // Standard Option patterns (these have always been the right way)
    let option = Some(42);

    // Extract value
    let value = option.unwrap(); // Standard
    println!("✓ unwrap(): {}", value);

    // Safe extraction
    let safe_value = option.unwrap_or(0);
    println!("✓ unwrap_or(): {}", safe_value);

    // Reference access
    let ref_value = option.as_ref();
    println!("✓ as_ref(): {:?}", ref_value);

    println!();
}

/// Demonstrate Maybe<T> migration
fn demonstrate_maybe_migration() {
    println!("2. Maybe<T> Migration");
    println!("---------------------\n");

    let maybe = Maybe::Just(42);

    // BEFORE: Use Identity trait
    // let value = maybe.value();        // ❌ Deprecated
    // let try_value = maybe.try_value(); // ❌ Deprecated
    // let into_value = maybe.into_value(); // ❌ Deprecated

    // AFTER: Use standard Rust patterns
    let value = maybe.unwrap(); // Standard extraction
    println!("✓ unwrap(): {}", value);

    // Create new Maybe for next examples
    let maybe = Maybe::Just(42);

    let safe_value = maybe.unwrap_or(0); // Safe default
    println!("✓ unwrap_or(): {}", safe_value);

    // Create new Maybe for reference access
    let maybe = Maybe::Just(42);
    let ref_value = maybe.as_ref(); // Reference without consuming
    println!("✓ as_ref(): {:?}", ref_value);

    // Handle Nothing case
    let nothing = Maybe::<i32>::Nothing;
    let safe_nothing = nothing.unwrap_or(0);
    println!("✓ Nothing case unwrap_or(): {}", safe_nothing);

    println!();
}

/// Demonstrate Choice<T> migration
fn demonstrate_choice_migration() {
    println!("3. Choice<T> Migration");
    println!("----------------------\n");

    let choice = Choice::new(42, vec![84, 126]);

    // BEFORE: Use Identity trait
    // let value = choice.value();        // ❌ Deprecated
    // let try_value = choice.try_value(); // ❌ Deprecated

    // AFTER: Use first() for primary value access
    let value = choice.first().expect("Choice is not empty"); // Gets primary value
    println!("✓ first(): {}", value);

    // Create new Choice for safe extraction
    let choice = Choice::new(42, vec![84, 126]);
    let safe_value = choice.first().unwrap_or(&0);
    println!("✓ first().unwrap_or(): {}", safe_value);

    // Create new Choice for reference access
    let choice = Choice::new(42, vec![84, 126]);
    let ref_value = choice.first(); // Reference without consuming
    println!("✓ first(): {:?}", ref_value);

    // Empty choice handling
    let empty_choice: Choice<i32> = Choice::new_empty();
    let empty_safe = empty_choice.first().unwrap_or(&0);
    println!("✓ Empty choice first().unwrap_or(): {:?}", empty_safe);

    // Alternative: Use iter() to get first value
    let choice = Choice::new(42, vec![84, 126]);
    let iter_value = choice.iter().next().unwrap();
    println!("✓ iter().next(): {}", iter_value);

    println!();
}

/// Demonstrate Either<L, R> migration
fn demonstrate_either_migration() {
    println!("4. Either<L, R> Migration");
    println!("-------------------------\n");

    let either: Either<&str, i32> = Either::Right(42);

    // BEFORE: Use Identity trait
    // let value = either.value();        // ❌ Deprecated
    // let try_value = either.try_value(); // ❌ Deprecated

    // AFTER: Use standard patterns
    let value = either.unwrap(); // Extracts Right value or panics
    println!("✓ unwrap(): {}", value);

    // Create new Either for safe extraction
    let either: Either<&str, i32> = Either::Right(42);
    let safe_value = either.unwrap_or(0);
    println!("✓ unwrap_or(): {}", safe_value);

    // Create new Either for reference access
    let either: Either<&str, i32> = Either::Right(42);
    let ref_value = &either;
    println!("✓ as_ref(): {:?}", ref_value);

    // Left case handling
    let left_either = Either::Left("error");
    let left_safe = left_either.unwrap_or(&0);
    println!("✓ Left case unwrap_or(): {}", left_safe);

    println!();
}

/// Demonstrate Id<T> migration (special case - use Comonad)
fn demonstrate_id_migration() {
    println!("5. Id<T> Migration (Comonad Pattern)");
    println!("------------------------------------\n");

    let id = Id::new(42);

    // BEFORE: Use Identity trait
    // let value = id.value(); // ❌ Deprecated

    // AFTER: Use Comonad for total extraction
    let value = id.extract(); // Guaranteed to succeed
    println!("✓ extract(): {}", value);

    // You can still use unwrap() for consistency
    let id = Id::new(42);
    let unwrap_value = id.unwrap();
    println!("✓ unwrap(): {}", unwrap_value);

    // Reference access
    let id = Id::new(42);
    let ref_value = id.as_ref();
    println!("✓ as_ref(): {:?}", ref_value);

    println!();
}

/// Demonstrate when to use Comonad vs unwrap()
fn demonstrate_comonad_usage() {
    println!("6. Comonad Usage Pattern");
    println!("------------------------\n");

    // Comonad is for types with GUARANTEED total extraction
    println!("✓ Use Comonad::extract() when extraction is guaranteed:");

    let id = Id::new("always present");
    let extracted = id.extract();
    println!("  Id::extract() = '{}' (always succeeds)", extracted);

    // unwrap() is for types with PARTIAL extraction
    println!("\n✓ Use unwrap() when extraction might fail:");

    let maybe = Maybe::Just("sometimes present");
    let unwrapped = maybe.unwrap(); // Could panic if Nothing
    println!("  Maybe::unwrap() = '{}' (may panic)", unwrapped);

    // unwrap_or() for safe partial extraction
    let nothing = Maybe::<&str>::Nothing;
    let safe = nothing.unwrap_or(&"default");
    println!("  Maybe::unwrap_or() = '{}' (safe default)", safe);

    println!();
}

/// Demonstrate best practices for value extraction
fn demonstrate_best_practices() {
    println!("7. Best Practices");
    println!("-----------------\n");

    println!("✓ Pattern 1: Use unwrap() when you're sure the value exists");
    let config = Maybe::Just("production");
    let env = config.unwrap(); // We know config is set
    println!("  Environment: {}", env);

    println!("\n✓ Pattern 2: Use unwrap_or() for safe defaults");
    let user_setting = Maybe::<String>::Nothing;
    let timeout = user_setting.unwrap_or("30s".to_string());
    println!("  Timeout: {} (default applied)", timeout);

    println!("\n✓ Pattern 3: Use as_ref() when you need to keep the original");
    let cache = Maybe::Just("redis://localhost");
    if let Some(cache_url) = cache.as_ref() {
        println!("  Cache URL: {} (original preserved)", cache_url);
        // cache is still available for later use
    }

    println!("\n✓ Pattern 4: Use Comonad::extract() for algebraic types");
    let computation = Id::new(42 * 2);
    let result = computation.extract();
    println!("  Computation result: {} (total extraction)", result);

    println!("\n✓ Pattern 5: Match for exhaustive handling");
    let either: Either<&str, i32> = Either::Left("error occurred");
    match either {
        Either::Right(value) => println!("  Success: {}", value),
        Either::Left(error) => println!("  Error: {}", error),
    }

    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maybe_migration() {
        let maybe = Maybe::Just(42);
        assert_eq!(maybe.unwrap(), 42);
        assert_eq!(maybe.unwrap_or(0), 42);

        let nothing = Maybe::<i32>::Nothing;
        assert_eq!(nothing.unwrap_or(0), 0);
    }

    #[test]
    fn test_choice_migration() {
        let choice = Choice::new(42, vec![84]);
        assert_eq!(choice.first(), Some(&42));
        assert_eq!(choice.first().unwrap_or(&0), &42);

        let empty: Choice<i32> = Choice::new_empty();
        assert_eq!(empty.first().unwrap_or(&0), &0);
    }

    #[test]
    fn test_either_migration() {
        let right: Either<&str, i32> = Either::Right(42);
        assert_eq!(right.unwrap(), 42);
        assert_eq!(right.unwrap_or(0), 42);

        let left = Either::Left("error");
        assert_eq!(left.unwrap_or(0), 0);
    }

    #[test]
    fn test_id_comonad() {
        let id = Id::new(42);
        assert_eq!(id.extract(), 42);
        assert_eq!(id.unwrap(), 42);
    }

    #[test]
    fn test_reference_preservation() {
        let maybe = Maybe::Just(42);
        let ref_val = maybe.as_ref();
        assert_eq!(ref_val, Some(&42));

        // Original is still available
        assert_eq!(maybe.unwrap(), 42);
    }
}
