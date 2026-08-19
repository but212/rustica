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
