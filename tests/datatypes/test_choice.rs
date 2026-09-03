use rustica::datatypes::choice::Choice;
use rustica::prelude::*;

#[test]
fn test_monad_laws() {
    let m = Choice::new(1, vec![2]);
    let f = |x: &i32| Choice::new(x + 1, vec![]);
    let g = |x: &i32| Choice::new(x * 2, vec![]);

    assert_eq!(Choice::<i32>::pure(&10).bind(f), f(&10));
    assert_eq!(m.bind(Choice::<i32>::pure), m);
    assert_eq!(m.bind(f).bind(g), m.bind(|x| f(x).bind(g)));
}

#[test]
fn test_choice_always_has_primary() {
    let c = Choice::new(1, vec![2, 3]);
    let primary: &i32 = c.first();
    assert_eq!(*primary, 1);
    assert_eq!(*c.primary(), 1);
    assert_eq!(c.alternatives(), &[2, 3]);
    assert_eq!(c.len(), 3);
    assert!(!c.is_empty());
}

#[test]
fn choice_try_from_rejects_empty_and_preserves_order() {
    let empty: Result<Choice<i32>, _> = Vec::new().try_into();
    assert_eq!(
        empty,
        Err(rustica::datatypes::error::ChoiceError::EmptyInput)
    );
    let empty_slice: Result<Choice<i32>, _> = (&[][..]).try_into();
    assert_eq!(
        empty_slice,
        Err(rustica::datatypes::error::ChoiceError::EmptyInput)
    );

    let choice: Choice<i32> = vec![10, 20, 30].try_into().unwrap();
    assert_eq!(choice.iter().copied().collect::<Vec<_>>(), vec![10, 20, 30]);

    let values = [40, 50];
    let choice: Choice<i32> = (&values[..]).try_into().unwrap();
    assert_eq!(choice.iter().copied().collect::<Vec<_>>(), vec![40, 50]);
}

#[test]
fn test_choice_of_many() {
    assert_eq!(Choice::of_many(Vec::<i32>::new()), None);
    let c = Choice::of_many(vec![10, 20, 30]).expect("should be non-empty");
    assert_eq!(*c.first(), 10);
    assert_eq!(c.alternatives(), &[20, 30]);
}

#[test]
fn test_choice_filter_values() {
    let c = Choice::new(1, vec![2, 3, 4]);
    let evens = c.filter_values(|&x| x % 2 == 0).expect("should have evens");
    assert_eq!(*evens.first(), 2);
    assert_eq!(evens.alternatives(), &[4]);

    let none = c.filter_values(|&x| x > 100);
    assert_eq!(none, None);
}
