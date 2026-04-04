use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;
use rustica::traits::bifunctor::Bifunctor;
use rustica::traits::hkt::{BinaryHKT, HKT};

// --- Functor Laws ---

#[quickcheck]
fn functor_identity_law(x: TestFunctor<i32>) -> bool {
    x.fmap(|&a| a) == x
}

#[quickcheck]
fn functor_composition_law(x: TestFunctor<i32>) -> bool {
    let f = |&a: &i32| a.saturating_add(1);
    let g = |&a: &i32| a.saturating_mul(2);
    x.fmap(|&a| f(&g(&a))) == x.fmap(g).fmap(f)
}

// --- Applicative Laws ---

#[quickcheck]
fn applicative_identity_law(x: TestFunctor<i32>) -> bool {
    let id = |x: &i32| *x;
    TestFunctor::<fn(&i32) -> i32>::pure(&id).apply(&x) == x
}

#[quickcheck]
fn applicative_homomorphism_law(val: i32) -> bool {
    let f = |x: &i32| x.saturating_add(1);
    let pure_f = TestFunctor::<fn(&i32) -> i32>::pure(&f);
    let pure_val = TestFunctor::<i32>::pure(&val);

    pure_f.apply(&pure_val) == TestFunctor::new(f(&val))
}

// --- Monad Laws ---

#[quickcheck]
fn monad_left_identity_law(val: i32) -> bool {
    let f = |&x: &i32| TestFunctor::new(x.saturating_add(1));
    TestFunctor::<i32>::pure(&val).bind(f) == f(&val)
}

#[quickcheck]
fn monad_associativity_law(x: TestFunctor<i32>) -> bool {
    let f = |&a: &i32| TestFunctor::new(a.saturating_add(1));
    let g = |&a: &i32| TestFunctor::new(a.saturating_mul(2));

    x.bind(f).bind(g) == x.bind(|&a| f(&a).bind(g))
}

// --- Bifunctor Laws ---

#[derive(Clone, Debug, PartialEq)]
struct TestBifunctor<A, B>(A, B);

impl<A, B> HKT for TestBifunctor<A, B> {
    type Source = A;
    type Output<U> = TestBifunctor<U, B>;
}

impl<A, B> BinaryHKT for TestBifunctor<A, B> {
    type Source2 = B;
    type BinaryOutput<U, V> = TestBifunctor<U, V>;

    fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<A, NewType2>
    where
        F: Fn(&Self::Source2) -> NewType2,
        A: Clone,
    {
        TestBifunctor(self.0.clone(), f(&self.1))
    }

    fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<A, NewType2>
    where
        F: Fn(Self::Source2) -> NewType2,
    {
        TestBifunctor(self.0, f(self.1))
    }
}

impl<A: Clone, B: Clone> Bifunctor for TestBifunctor<A, B> {
    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, B>
    where
        F: Fn(&A) -> C,
    {
        TestBifunctor(f(&self.0), self.1.clone())
    }
    fn second<D, G>(&self, g: G) -> Self::BinaryOutput<A, D>
    where
        G: Fn(&B) -> D,
    {
        TestBifunctor(self.0.clone(), g(&self.1))
    }
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&A) -> C,
        G: Fn(&B) -> D,
    {
        TestBifunctor(f(&self.0), g(&self.1))
    }
}

#[test]
fn bifunctor_identity_and_consistency() {
    let bf = TestBifunctor(10, 20);
    // Identity
    assert_eq!(bf.bimap(|&a| a, |&b| b), bf);
    // Comparison
    let f = |&a: &i32| a + 1;
    let g = |&b: &i32| b * 2;
    assert_eq!(bf.bimap(f, |&b| b), bf.first(f));
    assert_eq!(bf.bimap(|&a| a, g), bf.second(g));
}
