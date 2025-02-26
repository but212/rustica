use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;

#[quickcheck]
fn functor_identity(x: TestFunctor<i32>) -> bool {
    let id: &dyn Fn(&i32) -> i32 = &|x| *x;
    x.fmap(id) == x
}

#[quickcheck]
fn functor_composition(x: TestFunctor<i32>) -> bool {
    let f: &dyn Fn(&i32) -> i32 = &|x| x.saturating_add(1);
    let g: &dyn Fn(&i32) -> i32 = &|x| x.saturating_mul(2);
    let h: &dyn Fn(&i32) -> i32 = &|x| g(&f(x));
    x.fmap(f).fmap(g) == x.fmap(h)
}
