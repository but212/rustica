#[cfg(feature = "advanced")]
mod test_choice {
    use rustica::datatypes::choice::Choice;
    use rustica::prelude::*;

    #[test]
    fn test_choice_creation_and_access() {
        let choice = Choice::new(1, vec![2, 3, 4]);
        assert_eq!(*choice.first(), 1);
        assert_eq!(choice.alternatives(), &vec![2, 3, 4]);
        assert!(choice.has_alternatives());

        let single = Choice::new(1, vec![]);
        assert_eq!(*single.first(), 1);
        assert!(single.alternatives().is_empty());
        assert!(!single.has_alternatives());
    }

    #[test]
    fn test_choice_functor() {
        let choice = Choice::new(1, vec![2, 3, 4]);
        let doubled = choice.fmap(|x| x * 2);
        assert_eq!(*doubled.first(), 2);
        assert_eq!(doubled.alternatives(), &vec![4, 6, 8]);
    }

    #[test]
    fn test_choice_pure() {
        let choice: Choice<i32> = Choice::<i32>::pure(&42);
        assert_eq!(*choice.first(), 42);
        assert!(choice.alternatives().is_empty());
    }

    #[test]
    fn test_choice_applicative() {
        let choice = Choice::new(2, vec![3, 4]);
        let double = Box::new(|x: &i32| x * 2) as Box<dyn Fn(&i32) -> i32>;
        let triple = Box::new(|x: &i32| x * 3) as Box<dyn Fn(&i32) -> i32>;
        let f = Choice::new(double, vec![triple]);
        let result = choice.apply(&f);
        assert_eq!(*result.first(), 4);
        assert_eq!(result.alternatives(), &vec![6, 6, 8, 9, 12]);
    }

    #[test]
    fn test_choice_lift2() {
        let a = Choice::new(2, vec![3, 4]);
        let b = Choice::new(5, vec![6, 7]);
        let result = a.lift2(&b, |x, y| x + y);
        assert_eq!(*result.first(), 7);
        assert_eq!(result.alternatives(), &vec![8, 9, 8, 9, 9, 10, 10, 11]);
    }

    #[test]
    fn test_choice_lift3() {
        let a = Choice::new(2, vec![3]);
        let b = Choice::new(5, vec![6]);
        let c = Choice::new(10, vec![11]);
        let result = a.lift3(&b, &c, |x, y, z| x + y + z);
        assert_eq!(*result.first(), 17);
        assert_eq!(result.alternatives(), &vec![18, 18, 18, 19, 19, 19, 20]);
    }

    #[test]
    fn test_choice_monad() {
        let choice = Choice::new(2, vec![3, 4]);
        let result = choice.bind(|x| Choice::new(x * 2, vec![x * 3]));
        assert_eq!(*result.first(), 4);
        assert_eq!(result.alternatives(), &vec![6, 6, 9, 8, 12]);
    }

    #[test]
    fn test_choice_join() {
        let nested = Choice::new(Choice::new(1, vec![2, 3]), vec![Choice::new(4, vec![5, 6])]);
        let flattened = nested.join();
        assert_eq!(*flattened.first(), 1);
        assert_eq!(flattened.alternatives(), &vec![2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_choice_semigroup() {
        let a = Choice::new(1, vec![2, 3]);
        let b = Choice::new(4, vec![5, 6]);
        let combined = a.combine(&b);
        assert_eq!(*combined.first(), 1);
        assert_eq!(combined.alternatives(), &vec![2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_choice_monoid() {
        let empty: Choice<i32> = Choice::empty();
        assert_eq!(*empty.first(), 0);
        assert!(empty.alternatives().is_empty());

        let choice = Choice::new(1, vec![2, 3]);
        let combined = choice.combine(&empty);
        assert_eq!(*combined.first(), 1);
        assert_eq!(combined.alternatives(), &vec![2, 3, 0]);
    }
}
