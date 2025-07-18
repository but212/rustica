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

#[quickcheck]
fn functor_fmap_owned(x: TestFunctor<i32>) -> bool {
    let f = |x: i32| x.saturating_mul(2);
    let expected = TestFunctor::new(f(x.0));
    x.clone().fmap_owned(f) == expected
}

#[quickcheck]
fn functor_replace(x: TestFunctor<i32>, y: i32) -> bool {
    let replaced = x.replace(&y);
    replaced == TestFunctor::new(y)
}

#[quickcheck]
fn functor_replace_owned(x: TestFunctor<i32>, y: i32) -> bool {
    let replaced = x.replace_owned(y);
    replaced == TestFunctor::new(y)
}

#[quickcheck]
fn functor_void(x: TestFunctor<i32>) -> bool {
    let voided = x.void();
    voided == TestFunctor::new(())
}

#[quickcheck]
fn functor_void_owned(x: TestFunctor<i32>) -> bool {
    let voided = x.clone().void_owned();
    voided == TestFunctor::new(())
}

#[quickcheck]
fn functor_map_over_default(x: TestFunctor<i32>) -> bool {
    let f = |x: &i32| x.saturating_add(1);
    let mapped = x.fmap(f);
    mapped == TestFunctor::new(f(&x.0))
}
