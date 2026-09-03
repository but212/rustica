use rustica::datatypes::wrapper::{
    first::First, last::Last, max::Max, min::Min, predicate::Predicate, product::Product, sum::Sum,
};
use rustica::traits::{functor::Functor, monoid::Monoid, semigroup::Semigroup};

#[test]
fn arithmetic_wrappers_satisfy_associativity_and_identity() {
    let sum = Sum(2).combine(&Sum(3)).combine(&Sum(4));
    assert_eq!(sum, Sum(2).combine(&Sum(3).combine(&Sum(4))));
    assert_eq!(Sum(2).combine(&Sum::empty()), Sum(2));
    assert_eq!(Sum::empty().combine(&Sum(2)), Sum(2));

    let product = Product(2).combine(&Product(3)).combine(&Product(4));
    assert_eq!(
        product,
        Product(2).combine(&Product(3).combine(&Product(4)))
    );
    assert_eq!(Product(2).combine(&Product::empty()), Product(2));
    assert_eq!(Product::empty().combine(&Product(2)), Product(2));

    assert_eq!(Min(1).combine(&Min(3)).combine(&Min(2)), Min(1));
    assert_eq!(Max(1).combine(&Max(3)).combine(&Max(2)), Max(3));
}

#[test]
fn option_wrappers_satisfy_associativity_and_identity() {
    let first = First(Some(1))
        .combine(&First(None))
        .combine(&First(Some(2)));
    assert_eq!(first, First(Some(1)));
    assert_eq!(
        First::<i32>::empty().combine(&First(Some(2))),
        First(Some(2))
    );
    assert_eq!(First(Some(2)).combine(&First::empty()), First(Some(2)));

    let last = Last(Some(1)).combine(&Last(None)).combine(&Last(Some(2)));
    assert_eq!(last, Last(Some(2)));
    assert_eq!(Last::<i32>::empty().combine(&Last(Some(2))), Last(Some(2)));
    assert_eq!(Last(Some(2)).combine(&Last::empty()), Last(Some(2)));
}

#[test]
fn functor_identity_and_composition_are_preserved() {
    assert_eq!(Sum(4).fmap(|x| *x), Sum(4));
    assert_eq!(Product(4).fmap(|x| *x), Product(4));
    assert_eq!(First(Some(4)).fmap(|x| *x), First(Some(4)));
    assert_eq!(Last::<i32>(None).fmap(|x| *x), Last(None));
}

#[test]
fn predicates_cover_boolean_operations_and_identity() {
    let even = Predicate::new(|x: &i32| x % 2 == 0);
    let positive = Predicate::new(|x: &i32| *x > 0);
    assert!(even.union(&positive).contains(&3));
    assert!(even.intersection(&positive).contains(&2));
    assert!(!even.intersection(&positive).contains(&3));
    assert!(!even.diff(&positive).contains(&2));
    assert!(even.negate().contains(&3));
}
