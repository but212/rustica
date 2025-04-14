use rustica::datatypes::choice::Choice;
use rustica::prelude::*;

#[test]
fn test_choice_creation_and_access() {
    let choice = Choice::new(1, vec![2, 3, 4]);
    assert_eq!(*choice.first().unwrap(), 1);
    assert_eq!(choice.alternatives(), &[2, 3, 4]);
    assert!(choice.has_alternatives());

    let single = Choice::new(1, vec![]);
    assert_eq!(*single.first().unwrap(), 1);
    assert!(single.alternatives().is_empty());
    assert!(!single.has_alternatives());
}

#[test]
fn test_choice_functor() {
    let choice = Choice::new(1, vec![2, 3, 4]);

    // Test fmap
    let doubled = choice.fmap(|x| x * 2);
    assert_eq!(*doubled.first().unwrap(), 2);
    assert_eq!(doubled.alternatives(), &[4, 6, 8]);

    // Test fmap_owned
    let doubled_owned = choice.fmap_owned(|x| x * 2);
    assert_eq!(*doubled_owned.first().unwrap(), 2);
    assert_eq!(doubled_owned.alternatives(), &[4, 6, 8]);
}

#[test]
fn test_choice_pure() {
    let choice: Choice<i32> = Choice::<i32>::pure(&42);
    assert_eq!(*choice.first().unwrap(), 42);
    assert!(choice.alternatives().is_empty());
}

#[test]
fn test_choice_applicative() {
    let choice = Choice::new(2, vec![3, 4]);

    // Define the function type explicitly
    type FnType = fn(&i32) -> i32;
    type FnOwnedType = fn(i32) -> i32;

    // Use the same function type for both functions
    let double: FnType = |x| x * 2;
    let triple: FnType = |x| x * 3;

    let double_owned: FnOwnedType = |x| x * 2;
    let triple_owned: FnOwnedType = |x| x * 3;

    // Test apply
    let f = Choice::new(double, vec![triple]);
    let result = choice.apply(&f);
    assert_eq!(*result.first().unwrap(), 4);
    assert_eq!(result.alternatives(), &[6, 6, 9, 8, 12]);

    // Test apply_owned
    let f_owned = Choice::new(double_owned, vec![triple_owned]);
    let result_owned = choice.apply_owned(f_owned);
    assert_eq!(*result_owned.first().unwrap(), 4);
    assert_eq!(result_owned.alternatives(), &[9, 6, 9, 8, 12]);
}

#[test]
fn test_choice_lift2() {
    let a = Choice::new(2, vec![3, 4]);
    let b = Choice::new(5, vec![6, 7]);

    // Test lift2
    let result = a.lift2(&b, |x, y| x + y);
    assert_eq!(*result.first().unwrap(), 7);

    // Check if the same elements are included regardless of order
    let actual: Vec<_> = result.alternatives().to_vec();
    let expected = vec![8, 9, 8, 9, 9, 10, 10, 11];

    // Sort and compare
    let mut sorted_actual = actual;
    sorted_actual.sort();
    let mut sorted_expected = expected.clone();
    sorted_expected.sort();
    assert_eq!(sorted_actual, sorted_expected);

    // Test lift2_owned
    let owned_result = a.lift2_owned(b, |x, y| x + y);
    assert_eq!(*owned_result.first().unwrap(), 7);

    // Check owned version alternatives
    let owned_actual: Vec<_> = owned_result.alternatives().to_vec();
    let mut sorted_owned_actual = owned_actual;
    sorted_owned_actual.sort();
    assert_eq!(sorted_owned_actual, sorted_expected);
}

#[test]
fn test_choice_lift3() {
    let a = Choice::new(2, vec![3, 4]);
    let b = Choice::new(5, vec![6, 7]);
    let c = Choice::new(10, vec![20, 30]);

    // Test lift3
    let result = a.lift3(&b, &c, |x, y, z| x + y + z);

    assert_eq!(*result.first().unwrap(), 17);

    // Check if the same elements are included regardless of order
    let actual: Vec<_> = result.alternatives().to_vec();
    let expected = vec![
        18, 19, 20, 21, 27, 28, 29, 30, 31, 37, 38, 39, 40, 41, 18, 19, 20, 28, 29, 30, 38, 39, 40,
        19, 29, 39,
    ];

    // Sort and compare
    let mut sorted_actual = actual;
    sorted_actual.sort();
    let mut sorted_expected = expected.clone();
    sorted_expected.sort();
    assert_eq!(sorted_actual, sorted_expected);

    // Test lift3_owned
    let owned_result = a.lift3_owned(b, c, |x, y, z| x + y + z);
    assert_eq!(*owned_result.first().unwrap(), 17);

    // Check owned version alternatives
    let owned_actual: Vec<_> = owned_result.alternatives().to_vec();
    let mut sorted_owned_actual = owned_actual;
    sorted_owned_actual.sort();
    assert_eq!(sorted_owned_actual, sorted_expected);
}

#[test]
fn test_choice_monad() {
    let choice = Choice::new(2, vec![3, 4]);
    let result = choice.bind(|x| Choice::new(x * 2, vec![x * 3]));
    assert_eq!(*result.first().unwrap(), 4);
    assert_eq!(result.alternatives(), &[6, 6, 9, 8, 12]);
}

#[test]
fn test_choice_join() {
    let nested = Choice::new(Choice::new(1, vec![2, 3]), vec![Choice::new(4, vec![5, 6])]);
    let flattened = nested.join();
    assert_eq!(*flattened.first().unwrap(), 1);
    assert_eq!(flattened.alternatives(), &[2, 3, 4, 5, 6]);
}

#[test]
fn test_choice_semigroup() {
    let a = Choice::new(1, vec![2, 3]);
    let b = Choice::new(4, vec![5, 6]);
    let combined = a.combine(&b);
    assert_eq!(*combined.first().unwrap(), 1);
    assert_eq!(combined.alternatives(), &[2, 3, 4, 5, 6]);
}

#[test]
fn test_choice_monoid() {
    let empty: Choice<i32> = Choice::new_empty();
    assert!(empty.is_empty());
    assert!(empty.alternatives().is_empty());

    let choice = Choice::new(1, vec![2, 3]);
    let combined = choice.combine(&empty);
    assert_eq!(*combined.first().unwrap(), 1);
    assert_eq!(combined.alternatives(), &[2, 3]);

    let combined_empty_first = empty.combine(&choice);
    assert_eq!(*combined_empty_first.first().unwrap(), 1);
    assert_eq!(combined_empty_first.alternatives(), &[2, 3]);

    let empty2: Choice<i32> = Choice::new_empty();
    let combined_empties = empty.combine(&empty2);
    assert!(combined_empties.is_empty());
    assert!(combined_empties.alternatives().is_empty());
}

#[test]
fn test_choice_empty_and_len() {
    let empty: Choice<i32> = Choice::new_empty();
    assert!(empty.is_empty(), "new_empty should create an empty Choice");
    assert_eq!(empty.len(), 0, "Empty Choice should have length 0");

    let single = Choice::new(1, vec![]);
    assert!(
        !single.is_empty(),
        "Single element Choice should not be empty"
    );
    assert_eq!(
        single.len(),
        1,
        "Single element Choice should have length 1"
    );

    let multi = Choice::new(1, vec![2, 3]);
    assert!(
        !multi.is_empty(),
        "Multi element Choice should not be empty"
    );
    assert_eq!(multi.len(), 3, "Multi element Choice should have length 3");
}

#[test]
fn test_choice_add_alternatives() {
    let mut choice = Choice::new(1, vec![2]);
    choice = choice.add_alternatives(vec![3, 4]);
    assert_eq!(*choice.first().unwrap(), 1);
    assert_eq!(choice.alternatives(), &[2, 3, 4]);
    assert_eq!(choice.len(), 4);

    // Add to an empty alternative list
    let mut choice_single = Choice::new(1, vec![]);
    choice_single = choice_single.add_alternatives(vec![5, 6]);
    assert_eq!(*choice_single.first().unwrap(), 1);
    assert_eq!(choice_single.alternatives(), &[5, 6]);
    assert_eq!(choice_single.len(), 3);

    // Add empty list (should not change)
    let mut choice_no_add = Choice::new(1, vec![2]);
    choice_no_add = choice_no_add.add_alternatives(vec![]);
    assert_eq!(*choice_no_add.first().unwrap(), 1);
    assert_eq!(choice_no_add.alternatives(), &[2]);
    assert_eq!(choice_no_add.len(), 2);
}

#[test]
fn test_choice_remove_alternative() {
    let choice = Choice::new(1, vec![2, 3, 4, 5]);

    // Remove middle
    let removed_middle = choice.remove_alternative(1); // Remove '3' at index 1
    assert_eq!(*removed_middle.first().unwrap(), 1);
    assert_eq!(removed_middle.alternatives(), &[2, 4, 5]);
    assert_eq!(removed_middle.len(), 4);

    // Remove first alternative
    let removed_first = choice.remove_alternative(0); // Remove '2' at index 0
    assert_eq!(*removed_first.first().unwrap(), 1);
    assert_eq!(removed_first.alternatives(), &[3, 4, 5]);
    assert_eq!(removed_first.len(), 4);

    // Remove last alternative
    let removed_last = choice.remove_alternative(3); // Remove '5' at index 3
    assert_eq!(*removed_last.first().unwrap(), 1);
    assert_eq!(removed_last.alternatives(), &[2, 3, 4]);
    assert_eq!(removed_last.len(), 4);

    // Remove only alternative
    let single_alt = Choice::new(1, vec![2]);
    let removed_only = single_alt.remove_alternative(0);
    assert_eq!(*removed_only.first().unwrap(), 1);
    assert!(removed_only.alternatives().is_empty());
    assert!(!removed_only.has_alternatives());
    assert_eq!(removed_only.len(), 1);
}

#[test]
#[should_panic(expected = "Index out of bounds: the len is 2 but the index is 2")]
fn test_choice_remove_alternative_panic_out_of_bounds() {
    let choice = Choice::new(1, vec![2, 3]);
    // Remove at index 2, alternatives len is 2 (indices 0, 1)
    choice.remove_alternative(2);
}

#[test]
#[should_panic(expected = "Cannot remove alternative from Choice with no alternatives")]
fn test_choice_remove_alternative_panic_no_alternatives() {
    let choice: Choice<i32> = Choice::new(1, vec![]);
    choice.remove_alternative(0);
}

#[test]
fn test_choice_swap_with_alternative() {
    let choice = Choice::new(1, vec![2, 3, 4, 5]);

    // Swap with middle
    let swapped_middle = choice.clone().swap_with_alternative(1); // Swap 1 with 3 (index 1)
    assert_eq!(*swapped_middle.first().unwrap(), 3);
    assert_eq!(swapped_middle.alternatives(), &[2, 1, 4, 5]);
    assert_eq!(swapped_middle.len(), 5);

    // Swap with first alternative
    let swapped_first = choice.clone().swap_with_alternative(0); // Swap 1 with 2 (index 0)
    assert_eq!(*swapped_first.first().unwrap(), 2);
    assert_eq!(swapped_first.alternatives(), &[1, 3, 4, 5]);
    assert_eq!(swapped_first.len(), 5);

    // Swap with last alternative
    let swapped_last = choice.clone().swap_with_alternative(3); // Swap 1 with 5 (index 3)
    assert_eq!(*swapped_last.first().unwrap(), 5);
    assert_eq!(swapped_last.alternatives(), &[2, 3, 4, 1]);
    assert_eq!(swapped_last.len(), 5);

    // Swap with only alternative
    let single_alt = Choice::new(1, vec![2]);
    let swapped_only = single_alt.swap_with_alternative(0);
    assert_eq!(*swapped_only.first().unwrap(), 2);
    assert_eq!(swapped_only.alternatives(), &[1]);
    assert_eq!(swapped_only.len(), 2);
}

#[test]
#[should_panic(expected = "Index out of bounds: the len is 2 but the index is 2")]
fn test_choice_swap_with_alternative_panic_out_of_bounds() {
    let choice = Choice::new(1, vec![2, 3]);
    // Swap at index 2, alternatives len is 2 (indices 0, 1)
    choice.swap_with_alternative(2);
}

#[test]
#[should_panic(expected = "Cannot swap with alternative from Choice with no alternatives")]
fn test_choice_swap_with_alternative_panic_no_alternatives() {
    let choice: Choice<i32> = Choice::new(1, vec![]);
    choice.swap_with_alternative(0);
}

#[test]
fn test_choice_filter() {
    let choice = Choice::new(2, vec![1, 3, 4, 5, 6]);

    // Filter evens (primary survives)
    let evens = choice.filter(|&x| x % 2 == 0);
    assert_eq!(*evens.first().unwrap(), 2);
    assert_eq!(evens.alternatives(), &[4, 6]);
    assert_eq!(evens.len(), 3);

    // Filter odds (primary is filtered out, first alternative becomes primary)
    let odds = choice.filter(|&x| x % 2 != 0);
    assert_eq!(*odds.first().unwrap(), 1);
    assert_eq!(odds.alternatives(), &[3, 5]);
    assert_eq!(odds.len(), 3);

    // Filter everything (results in empty Choice)
    let none = choice.filter(|_| false);
    assert!(none.is_empty());
    assert!(none.alternatives().is_empty());
    assert_eq!(none.len(), 0);

    // Filter nothing (returns original)
    let all = choice.filter(|_| true);
    assert_eq!(*all.first().unwrap(), 2);
    assert_eq!(all.alternatives(), &[1, 3, 4, 5, 6]);
    assert_eq!(all.len(), 6);

    // Filter on a Choice with only a primary value
    let single = Choice::new(10, vec![]);
    let single_filtered_out = single.filter(|&x| x < 5);
    assert!(single_filtered_out.is_empty());
    let single_kept = single.filter(|&x| x > 5);
    assert_eq!(*single_kept.first().unwrap(), 10);
    assert!(single_kept.alternatives().is_empty());
    assert_eq!(single_kept.len(), 1);
}

#[test]
fn test_choice_fmap_alternatives() {
    let choice = Choice::new(1, vec![2, 3, 4]);

    // Double alternatives
    let doubled = choice.fmap_alternatives(|&x| x * 2);
    assert_eq!(*doubled.first().unwrap(), 1); // Primary unchanged
    assert_eq!(doubled.alternatives(), &[4, 6, 8]);

    // Map on Choice with no alternatives (should not change)
    let single = Choice::new(10, vec![]);
    let single_mapped = single.fmap_alternatives(|&x| x * 2);
    assert_eq!(*single_mapped.first().unwrap(), 10);
    assert!(single_mapped.alternatives().is_empty());
}

#[test]
fn test_choice_filter_values() {
    let choice = Choice::new(2, vec![1, 3, 4, 5, 6]);

    // Filter evens (primary survives)
    let evens: Choice<i32> = choice.filter_values(|&x| x % 2 == 0);
    assert_eq!(*evens.first().unwrap(), 2);
    assert_eq!(evens.alternatives(), &[4, 6]);
    assert_eq!(evens.len(), 3);

    // Filter odds (primary is filtered out)
    let odds: Choice<i32> = choice.filter_values(|&x| x % 2 != 0);
    assert_eq!(*odds.first().unwrap(), 1);
    assert_eq!(odds.alternatives(), &[3, 5]);
    assert_eq!(odds.len(), 3);

    // Filter everything (results in empty Choice)
    let none: Choice<i32> = choice.filter_values(|_| false);
    assert!(none.is_empty());
    assert!(none.alternatives().is_empty());
    assert_eq!(none.len(), 0);

    // Filter nothing (returns original)
    let all: Choice<i32> = choice.filter_values(|_| true);
    assert_eq!(*all.first().unwrap(), 2);
    assert_eq!(all.alternatives(), &[1, 3, 4, 5, 6]);
    assert_eq!(all.len(), 6);
}
