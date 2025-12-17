//! Tests for the Alternative trait

use rustica::traits::alternative::Alternative;

mod option_alternative {
    use super::*;

    #[test]
    fn test_empty_alt() {
        let empty: Option<i32> = Option::<i32>::empty_alt::<i32>();
        assert_eq!(empty, None);
    }

    #[test]
    fn test_alt_some_some() {
        let a = Some(1);
        let b = Some(2);
        assert_eq!(a.alt(&b), Some(1));
    }

    #[test]
    fn test_alt_none_some() {
        let a: Option<i32> = None;
        let b = Some(2);
        assert_eq!(a.alt(&b), Some(2));
    }

    #[test]
    fn test_alt_some_none() {
        let a = Some(1);
        let b: Option<i32> = None;
        assert_eq!(a.alt(&b), Some(1));
    }

    #[test]
    fn test_alt_none_none() {
        let a: Option<i32> = None;
        let b: Option<i32> = None;
        assert_eq!(a.alt(&b), None);
    }

    #[test]
    fn test_guard_true() {
        assert_eq!(Option::<i32>::guard(true), Some(()));
    }

    #[test]
    fn test_guard_false() {
        assert_eq!(Option::<i32>::guard(false), None);
    }

    #[test]
    fn test_many_some() {
        let some = Some(42);
        assert_eq!(some.many(), Some(vec![42]));
    }

    #[test]
    fn test_many_none() {
        let none: Option<i32> = None;
        assert_eq!(none.many(), None);
    }

    #[test]
    fn test_left_identity_law() {
        let x = Some(42);
        let empty: Option<i32> = Option::<i32>::empty_alt::<i32>();
        assert_eq!(empty.alt(&x), x);
    }

    #[test]
    fn test_right_identity_law() {
        let x = Some(42);
        let empty: Option<i32> = Option::<i32>::empty_alt::<i32>();
        assert_eq!(x.alt(&empty), x);
    }

    #[test]
    fn test_associativity_law() {
        let a = Some(1);
        let b = Some(2);
        let c = Some(3);

        let left = a.alt(&b).alt(&c);
        let right = a.alt(&b.alt(&c));
        assert_eq!(left, right);
    }

    #[test]
    fn test_associativity_with_none() {
        let a: Option<i32> = None;
        let b = Some(2);
        let c = Some(3);

        let left = a.alt(&b).alt(&c);
        let right = a.alt(&b.alt(&c));
        assert_eq!(left, right);
    }
}

mod vec_alternative {
    use super::*;

    #[test]
    fn test_empty_alt() {
        let empty: Vec<i32> = Vec::<i32>::empty_alt::<i32>();
        assert_eq!(empty, Vec::<i32>::new());
    }

    #[test]
    fn test_alt_non_empty_non_empty() {
        let a = vec![1, 2];
        let b = vec![3, 4];
        assert_eq!(a.alt(&b), vec![1, 2]);
    }

    #[test]
    fn test_alt_empty_non_empty() {
        let a: Vec<i32> = Vec::new();
        let b = vec![3, 4];
        assert_eq!(a.alt(&b), vec![3, 4]);
    }

    #[test]
    fn test_alt_non_empty_empty() {
        let a = vec![1, 2];
        let b: Vec<i32> = Vec::new();
        assert_eq!(a.alt(&b), vec![1, 2]);
    }

    #[test]
    fn test_alt_empty_empty() {
        let a: Vec<i32> = Vec::new();
        let b: Vec<i32> = Vec::new();
        assert_eq!(a.alt(&b), Vec::<i32>::new());
    }

    #[test]
    fn test_guard_true() {
        assert_eq!(Vec::<i32>::guard(true), vec![()]);
    }

    #[test]
    fn test_guard_false() {
        assert_eq!(Vec::<i32>::guard(false), Vec::<()>::new());
    }

    #[test]
    fn test_many_non_empty() {
        let xs = vec![1, 2];
        assert_eq!(xs.many(), vec![vec![1, 2]]);
    }

    #[test]
    fn test_many_empty() {
        let empty: Vec<i32> = Vec::new();
        assert_eq!(empty.many(), Vec::<Vec<i32>>::new());
    }

    #[test]
    fn test_many_single() {
        let xs = vec![42];
        assert_eq!(xs.many(), vec![vec![42]]);
    }

    #[test]
    fn test_left_identity_law() {
        let x = vec![1, 2, 3];
        let empty: Vec<i32> = Vec::<i32>::empty_alt::<i32>();
        assert_eq!(empty.alt(&x), x);
    }

    #[test]
    fn test_right_identity_law() {
        let x = vec![1, 2, 3];
        let empty: Vec<i32> = Vec::<i32>::empty_alt::<i32>();
        assert_eq!(x.alt(&empty), x);
    }

    #[test]
    fn test_associativity_law() {
        let a = vec![1];
        let b = vec![2];
        let c = vec![3];

        let left = a.alt(&b).alt(&c);
        let right = a.alt(&b.alt(&c));
        assert_eq!(left, right);
    }

    #[test]
    fn test_associativity_with_empty() {
        let a: Vec<i32> = Vec::new();
        let b = vec![2];
        let c = vec![3];

        let left = a.alt(&b).alt(&c);
        let right = a.alt(&b.alt(&c));
        assert_eq!(left, right);
    }
}
