#[cfg(feature = "advanced")]
mod test_choice {
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
            18, 19, 20, 21, 27, 28, 29, 30, 31, 37, 38, 39, 40, 41, 18, 19, 20, 28, 29, 30, 38, 39,
            40, 19, 29, 39,
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
        let empty: Choice<i32> = Choice::empty();
        assert_eq!(*empty.first().unwrap(), 0);
        assert!(empty.alternatives().is_empty());

        let choice = Choice::new(1, vec![2, 3]);
        let combined = choice.combine(&empty);
        assert_eq!(*combined.first().unwrap(), 1);
        assert_eq!(combined.alternatives(), &[2, 3, 0]);
    }
}
