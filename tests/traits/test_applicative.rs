use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;

#[quickcheck]
fn applicative_identity(x: TestFunctor<i32>) -> bool {
    let id_fun: &dyn Fn(&i32) -> i32 = &|x| *x;
    let pure_id = TestFunctor::<&dyn Fn(&i32) -> i32>::pure(id_fun);
    x.apply(&pure_id) == x
}

#[quickcheck]
fn applicative_composition(x: TestFunctor<i32>) -> bool {
    let f: &dyn Fn(&i32) -> i32 = &|x| x.saturating_add(1);
    let g: &dyn Fn(&i32) -> i32 = &|x| x.saturating_mul(2);
    let pure_f = TestFunctor::<&dyn Fn(&i32) -> i32>::pure(f);
    let pure_g = TestFunctor::<&dyn Fn(&i32) -> i32>::pure(g);
    let compose = |x: &i32| g(&f(x));
    let pure_compose = TestFunctor::<&dyn Fn(&i32) -> i32>::pure(&compose);
    x.apply(&pure_f).apply(&pure_g) == x.apply(&pure_compose)
}

#[quickcheck]
fn applicative_homomorphism(x: i32) -> bool {
    let f: &dyn Fn(&i32) -> i32 = &|x| x.saturating_add(1);
    let pure_x = TestFunctor::<i32>::pure(x);
    let pure_f = TestFunctor::<&dyn Fn(&i32) -> i32>::pure(f);
    pure_x.apply(&pure_f) == TestFunctor::<i32>::pure(f(&x))
}
