//! Choice<T> Migration Guide for v0.11.0
//!
//! This example demonstrates how to migrate from deprecated Choice<T> utility methods
//! to the new simplified API focusing on core categorical operations.
//!
//! ## What's Deprecated in v0.11.0
//!
//! The following methods are deprecated and will be removed in v0.12.0:
//! - Convenience methods: `has_alternatives()`, `to_vec()`, `find_first()`, `iter_alternatives()`
//! - Non-categorical operations: `dedup()`, `fold()`, `add_alternatives()`, index-based operations
//! - Semantically confusing methods: `filter()`, `flatten_sorted()`, `bind_lazy()`
//!
//! ## What's Retained
//!
//! Core categorical operations remain available:
//! - Creation: `Choice::new()`, `Choice::new_empty()`, `Choice::of_many()`
//! - Access: `first()`, `alternatives()`, `len()`, `is_empty()`
//! - Core operations: `filter_values()`, `flatten()`, `try_flatten()`, `iter()`
//! - All trait implementations: Functor, Applicative, Monad, MonadPlus, etc.

use rustica::datatypes::choice::Choice;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::semigroup::Semigroup;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

fn main() {
    println!("Choice<T> Migration Examples for v0.11.0");
    println!("==========================================\n");

    demonstrate_convenience_methods();
    demonstrate_non_categorical_operations();
    demonstrate_index_based_operations();
    demonstrate_semantically_confusing_methods();
    demonstrate_common_patterns();
    demonstrate_performance_considerations();
}

/// Demonstrate migration of convenience/redundant methods
fn demonstrate_convenience_methods() {
    println!("1. Convenience Methods Migration");
    println!("--------------------------------\n");

    let choice = Choice::new(1, vec![2, 3]);

    // BEFORE: Check for alternatives
    // if choice.has_alternatives() {  // ❌ Deprecated
    //     println!("Has alternatives");
    // }

    // AFTER: Check for alternatives
    if !choice.alternatives().is_empty() {
        // Clear semantics
        println!("✓ Has alternatives: {}", !choice.alternatives().is_empty());
    }

    // BEFORE: Convert to Vec
    // let vec = choice.to_vec();  // ❌ Deprecated

    // AFTER: Convert to Vec
    let vec: Vec<i32> = choice.iter().cloned().collect(); // Standard pattern
    println!("✓ Converted to Vec: {:?}", vec);

    // Re-create choice for next examples
    let choice = Choice::new(1, vec![2, 3, 4, 5]);

    // BEFORE: Find first matching
    // let found = choice.find_first(|&x| x > 2);  // ❌ Deprecated

    // AFTER: Find first matching
    let found = choice.iter().find(|&&x| x > 2); // Standard iterator
    println!("✓ First > 2: {:?}", found);

    // BEFORE: Iterate alternatives
    // for alt in choice.iter_alternatives() {  // ❌ Deprecated
    //     println!("Alt: {}", alt);
    // }

    // AFTER: Iterate alternatives
    print!("✓ Alternatives: ");
    for alt in choice.alternatives().iter() {
        // Direct slice access
        print!("{} ", alt);
    }
    println!("\n");
}

/// Demonstrate migration of non-categorical operations
fn demonstrate_non_categorical_operations() {
    println!("2. Non-Categorical Operations Migration");
    println!("---------------------------------------\n");

    let choice = Choice::new(1, vec![2, 3, 2, 4]);

    // BEFORE: Deduplication
    // let unique = choice.dedup();  // ❌ Deprecated
    // let unique_by_key = choice.dedup_by_key(|x| x % 2);  // ❌ Deprecated

    // AFTER: Deduplication - external iteration
    let unique: Choice<i32> = Choice::from_iter(
        choice
            .iter()
            .cloned()
            .collect::<HashSet<_>>() // Remove duplicates
            .into_iter(),
    ); // Convert back to Choice
    println!("✓ Unique values: {:?}", unique.iter().collect::<Vec<_>>());

    let unique_by_key: Choice<i32> = Choice::from_iter(
        choice
            .iter()
            .cloned()
            .map(|x| (x % 2, x))
            .collect::<HashMap<_, _>>() // Group by key
            .into_values(),
    );
    println!(
        "✓ Unique by key (x % 2): {:?}",
        unique_by_key.iter().collect::<Vec<_>>()
    );

    // BEFORE: Folding
    // let sum = choice.fold(0, |acc, &x| acc + x);  // ❌ Deprecated

    // AFTER: Folding - use Foldable trait
    let sum = choice.fold_left(&0, |acc, &x| acc + x); // Categorical
    println!("✓ Sum using fold_left: {}", sum);

    // BEFORE: Map conversion
    // let map = choice.to_map_with_key(|x| x % 2);  // ❌ Deprecated

    // AFTER: Map conversion - standard iterator pattern
    let map: HashMap<i32, Vec<i32>> = choice.iter().cloned().fold(HashMap::new(), |mut acc, x| {
        acc.entry(x % 2).or_insert_with(Vec::new).push(x);
        acc
    });
    println!("✓ Map (x % 2 -> x): {:?}", map);

    // BEFORE: Adding alternatives
    // let expanded = choice.add_alternatives(vec![5, 6]);  // ❌ Deprecated

    // AFTER: Adding alternatives - use Semigroup
    let expanded = choice.combine(&Choice::new(5, vec![6])); // Categorical
    println!(
        "✓ Combined with [5, 6]: {:?}",
        expanded.iter().collect::<Vec<_>>()
    );
    println!();
}

/// Demonstrate migration of index-based operations
fn demonstrate_index_based_operations() {
    println!("3. Index-Based Operations Migration");
    println!("-----------------------------------\n");

    let choice = Choice::new(1, vec![2, 3, 4]);

    // BEFORE: Remove by index
    // let removed = choice.remove_alternative(1);  // ❌ Deprecated
    // let safe_removed = choice.try_remove_alternative(1);  // ❌ Deprecated

    // AFTER: Remove by condition
    let removed = choice.filter_values(|&x| x != 3); // Clear semantics
    println!("✓ Remove value 3: {:?}", removed.iter().collect::<Vec<_>>());

    // For more complex removal logic, use external iteration
    let filtered: Choice<i32> = Choice::from_iter(
        choice
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != 2) // Skip index 2 (value 4)
            .map(|(_, &x)| x),
    );
    println!(
        "✓ Remove index 2: {:?}",
        filtered.iter().collect::<Vec<_>>()
    );

    // BEFORE: Swap with alternative
    // let swapped = choice.swap_with_alternative(0);  // ❌ Deprecated
    // let safe_swapped = choice.try_swap_with_alternative(0);  // ❌ Deprecated

    // AFTER: Swapping - use external patterns or restructure
    // If you need to promote an alternative to primary:
    let choice2 = Choice::new(3, vec![1, 2, 4]); // Explicit construction
    println!(
        "✓ Promote alternative to primary: {:?}",
        choice2.iter().collect::<Vec<_>>()
    );
    println!();
}

/// Demonstrate migration of semantically confusing/overly specialized methods
fn demonstrate_semantically_confusing_methods() {
    println!("4. Semantically Confusing Methods Migration");
    println!("--------------------------------------------\n");

    let choice = Choice::new(1, vec![2, 3, 4]);

    // BEFORE: Filter alternatives only (preserves primary unconditionally)
    // let filtered = choice.filter(|&x| x > 2);  // ❌ Deprecated - unclear semantics

    // AFTER: Filter all values (may change primary)
    let filtered = choice.filter_values(|&x| x > 2); // Clear semantics
    println!(
        "✓ Filter all values > 2: {:?}",
        filtered.iter().collect::<Vec<_>>()
    );

    // BEFORE: Map alternatives only
    // let mapped = choice.fmap_alternatives(|x| x * 2);  // ❌ Deprecated

    // AFTER: Map all values with conditional logic
    let mapped = choice.fmap(|&x| if x > 1 { x * 2 } else { x }); // Flexible
    println!("✓ Map values > 1: {:?}", mapped.iter().collect::<Vec<_>>());

    // BEFORE: Flatten with sorting
    // let nested = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
    // let sorted_flat = nested.flatten_sorted();  // ❌ Deprecated - mixed concerns

    // AFTER: Separate categorical and ordering concerns
    let nested = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
    let flattened = nested.flatten(); // Pure categorical
    let sorted_flat: Choice<i32> = {
        let mut sorted: Vec<i32> = flattened.iter().cloned().collect();
        sorted.sort();
        Choice::from_iter(sorted)
    }; // External
    println!(
        "✓ Flattened then sorted: {:?}",
        sorted_flat.iter().collect::<Vec<_>>()
    );

    // BEFORE: Lazy bind
    // let lazy_iter = choice.bind_lazy(|x| Choice::new(x * 2, vec![x * 3])); // ❌ Deprecated

    // AFTER: Use standard bind with iteration
    let eager: Choice<i32> = choice.bind(|&x| Choice::new(x * 2, vec![x * 3])); // Standard
    println!("✓ Bind eagerly: {:?}", eager.iter().collect::<Vec<_>>());

    let lazy_iter = choice.iter().flat_map(|&x| {
        let result = Choice::new(x * 2, vec![x * 3]);
        result.into_iter()
    }); // External lazy pattern
    println!(
        "✓ Bind lazily (first 5): {:?}",
        lazy_iter.take(5).collect::<Vec<_>>()
    );
    println!();
}

/// Demonstrate common migration patterns
fn demonstrate_common_patterns() {
    println!("5. Common Migration Patterns");
    println!("----------------------------\n");

    // Pattern 1: Collection Utilities
    println!("Pattern 1: Collection Utilities");
    println!("BEFORE - using Choice as a collection:");
    // let choice = Choice::new(1, vec![2, 3, 4, 5]);
    // let even = choice.filter(|&x| x % 2 == 0);
    // let unique = choice.dedup();
    // let sum = choice.fold(0, |acc, &x| acc + x);

    println!("AFTER - using Choice as a categorical structure:");
    let choice = Choice::new(1, vec![2, 3, 4, 5]);
    let even = choice.filter_values(|&x| x % 2 == 0); // Clear filtering
    println!("  Even numbers: {:?}", even.iter().collect::<Vec<_>>());

    let unique = Choice::from_iter(choice.iter().cloned().collect::<HashSet<_>>().into_iter());
    println!("  Unique numbers: {:?}", unique.iter().collect::<Vec<_>>());

    let sum = choice.fold_left(&0, |acc, &x| acc + x); // Categorical folding
    println!("  Sum: {}", sum);

    // Pattern 2: Index-Based Manipulation
    println!("\nPattern 2: Index-Based Manipulation");
    println!("BEFORE - index-based thinking:");
    // let choice = Choice::new(1, vec![2, 3, 4, 5]);
    // let without_third = choice.remove_alternative(2);
    // let with_swapped = choice.swap_with_alternative(0);

    println!("AFTER - value-based thinking:");
    let choice = Choice::new(1, vec![2, 3, 4, 5]);
    let without_third = choice.filter_values(|&x| x != 4); // Remove by value
    println!(
        "  Without value 4: {:?}",
        without_third.iter().collect::<Vec<_>>()
    );

    let with_swapped = Choice::new(2, vec![1, 3, 4, 5]); // Explicit construction
    println!(
        "  Promoted 2 to primary: {:?}",
        with_swapped.iter().collect::<Vec<_>>()
    );

    // Pattern 3: Mixed Operations
    println!("\nPattern 3: Mixed Operations");
    println!("BEFORE - mixing concerns:");
    // let choice = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
    // let result = choice.flatten_sorted();  // Mixes flatten + sort

    println!("AFTER - separate concerns:");
    let choice = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
    let flattened = choice.flatten(); // Pure categorical
    let result: Choice<i32> = {
        let mut sorted: Vec<i32> = flattened.iter().cloned().collect();
        sorted.sort();
        Choice::from_iter(sorted)
    }; // External ordering
    println!(
        "  Flattened then sorted: {:?}",
        result.iter().collect::<Vec<_>>()
    );
    println!();
}

/// Demonstrate performance considerations
fn demonstrate_performance_considerations() {
    println!("6. Performance Considerations");
    println!("-----------------------------\n");

    println!("BEFORE - optimized internal implementations:");
    println!("  choice.dedup()              // O(n) with internal HashSet");
    println!("  choice.flatten_sorted()     // O(n log n) with internal sort");

    println!("\nAFTER - external patterns (may be slightly less efficient):");
    println!("  choice.iter().cloned().collect::<HashSet<_>>().into_iter().collect()");
    println!("  // O(n) but more allocations");
    println!("  choice.flatten().into_iter().sorted().collect()");
    println!("  // O(n log n) but clearer");

    println!("\nTrade-offs:");
    println!("  + Clearer intent");
    println!("  + Standard Rust patterns");
    println!("  + Better composability");
    println!("  + Categorical purity");
    println!("  - Slightly more allocation overhead");

    println!("\nNote: If performance is critical, you can implement custom");
    println!("optimized functions for your specific use case.\n");

    println!("7. Temporary Compatibility");
    println!("-------------------------\n");
    println!("If you need time to migrate, you can temporarily allow deprecated warnings:");
    println!("```rust");
    println!("#![allow(deprecated)]");
    println!("");
    println!("// Your existing code will still compile with warnings");
    println!("// but you'll want to migrate before v0.12.0");
    println!("```");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convenience_methods_migration() {
        let choice = Choice::new(1, vec![2, 3]);

        // Test alternatives check
        assert!(!choice.alternatives().is_empty());

        // Test Vec conversion
        let vec: Vec<i32> = choice.clone().iter().cloned().collect();
        assert_eq!(vec, vec![1, 2, 3]);

        // Test find first
        let found = choice.iter().find(|&&x| x > 2);
        assert_eq!(found, Some(&3));
    }

    #[test]
    fn test_non_categorical_operations_migration() {
        let choice = Choice::new(1, vec![2, 3, 2, 4]);

        // Test deduplication
        let unique: Choice<i32> =
            Choice::from_iter(choice.iter().cloned().collect::<HashSet<_>>().into_iter());
        let unique_vals: Vec<i32> = unique.iter().cloned().collect();
        assert!(unique_vals.contains(&1));
        assert!(unique_vals.contains(&2));
        assert!(unique_vals.contains(&3));
        assert!(unique_vals.contains(&4));

        // Test folding
        let sum = choice.fold_left(&0, |acc, &x| acc + x);
        assert_eq!(sum, 12);
    }

    #[test]
    fn test_index_based_operations_migration() {
        let choice = Choice::new(1, vec![2, 3, 4]);

        // Test remove by condition
        let removed = choice.filter_values(|&x| x != 3);
        let removed_vals: Vec<i32> = removed.iter().cloned().collect();
        assert!(!removed_vals.contains(&3));
        assert!(removed_vals.contains(&1));
        assert!(removed_vals.contains(&2));
        assert!(removed_vals.contains(&4));
    }

    #[test]
    fn test_semantically_confusing_methods_migration() {
        let choice = Choice::new(1, vec![2, 3, 4]);

        // Test filter values
        let filtered = choice.filter_values(|&x| x > 2);
        let filtered_vals: Vec<i32> = filtered.iter().cloned().collect();
        for &val in &filtered_vals {
            assert!(val > 2);
        }

        // Test flatten with external sorting
        let nested = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
        let flattened = nested.flatten();
        let sorted_flat: Choice<i32> = {
            let mut sorted: Vec<i32> = flattened.iter().cloned().collect();
            sorted.sort();
            Choice::from_iter(sorted)
        };
        let sorted_vals: Vec<i32> = sorted_flat.iter().cloned().collect();
        let mut sorted_expected = sorted_vals.clone();
        sorted_expected.sort();
        assert_eq!(sorted_vals, sorted_expected);
    }
}
