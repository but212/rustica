use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;

#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let f: &dyn Fn(&i32) -> TestFunctor<i32> = &|x| TestFunctor::<i32>::pure(x.saturating_add(1));
    TestFunctor::<i32>::pure(x).bind(f) == f(&x)
}

#[quickcheck]
fn monad_right_identity(x: TestFunctor<i32>) -> bool {
    let pure: &dyn Fn(&i32) -> TestFunctor<i32> = &|x| TestFunctor::<i32>::pure(*x);
    x.bind(pure) == x
}

#[quickcheck]
fn monad_associativity(x: TestFunctor<i32>) -> bool {
    let f: &dyn Fn(&i32) -> TestFunctor<i32> = &|x| TestFunctor::<i32>::pure(x.saturating_add(1));
    let g: &dyn Fn(&i32) -> TestFunctor<i32> = &|x| TestFunctor::<i32>::pure(x.saturating_mul(2));
    let h: &dyn Fn(&i32) -> TestFunctor<i32> = &|x| f(x).bind(g);
    x.bind(f).bind(g) == x.bind(h)
}
