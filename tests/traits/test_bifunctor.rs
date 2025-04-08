use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;
use rustica::traits::bifunctor::Bifunctor;
use rustica::traits::hkt::{BinaryHKT, HKT};
use std::marker::PhantomData;

// TestBifunctor is a simple bifunctor implementation for testing
#[derive(Clone, Debug, PartialEq)]
pub struct TestBifunctor<A, B>(A, B, PhantomData<(A, B)>);

impl<A, B> TestBifunctor<A, B> {
    pub fn new(a: A, b: B) -> Self {
        TestBifunctor(a, b, PhantomData)
    }
}

// Implement HKT for TestBifunctor
impl<A, B> HKT for TestBifunctor<A, B> {
    type Source = A;
    type Output<U> = TestBifunctor<U, B>;
}

// Implement BinaryHKT for TestBifunctor
impl<A, B> BinaryHKT for TestBifunctor<A, B> {
    type Source2 = B;
    type BinaryOutput<U, V> = TestBifunctor<U, V>;

    fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<A, NewType2>
    where
        F: Fn(&Self::Source2) -> NewType2,
        A: Clone,
    {
        TestBifunctor::new(self.0.clone(), f(&self.1))
    }

    fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<A, NewType2>
    where
        F: Fn(Self::Source2) -> NewType2,
    {
        TestBifunctor::new(self.0, f(self.1))
    }
}

// Implement Bifunctor for TestBifunctor
impl<A: Clone, B: Clone> Bifunctor for TestBifunctor<A, B> {
    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, B>
    where
        F: Fn(&A) -> C,
    {
        TestBifunctor::new(f(&self.0), self.1.clone())
    }

    fn second<D, G>(&self, g: G) -> Self::BinaryOutput<A, D>
    where
        G: Fn(&B) -> D,
    {
        TestBifunctor::new(self.0.clone(), g(&self.1))
    }

    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&A) -> C,
        G: Fn(&B) -> D,
    {
        TestBifunctor::new(f(&self.0), g(&self.1))
    }
}

// Implement Arbitrary for TestBifunctor with constrained i32 values
impl Arbitrary for TestBifunctor<i32, i32> {
    fn arbitrary(g: &mut Gen) -> Self {
        // Constrain generated i32 to a smaller range to avoid overflow
        let left = (i32::arbitrary(g) % 1000) - 500;
        let right = (i32::arbitrary(g) % 1000) - 500;
        TestBifunctor::new(left, right)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let a = self.0;
        let b = self.1;
        Box::new(
            a.shrink()
                .flat_map(move |a_| {
                    b.shrink()
                        .map(move |b_| TestBifunctor::new(a_, b_))
                        .chain(std::iter::once(TestBifunctor::new(a_, b)))
                })
                .chain(b.shrink().map(move |b_| TestBifunctor::new(a, b_))),
        )
    }
}

// Test the identity law: bimap(id, id) == id
#[quickcheck]
fn bifunctor_identity_law(bf: TestBifunctor<i32, i32>) -> bool {
    let id_a: &dyn Fn(&i32) -> i32 = &|x| *x;
    let id_b: &dyn Fn(&i32) -> i32 = &|x| *x;

    let bimap_id_id = bf.bimap(id_a, id_b);
    bimap_id_id == bf
}

// Test that first and second can be implemented in terms of bimap
#[quickcheck]
fn bifunctor_first_second_consistent_with_bimap(bf: TestBifunctor<i32, i32>) -> bool {
    let f: &dyn Fn(&i32) -> i32 = &|x| x + 1;
    let id_b: &dyn Fn(&i32) -> i32 = &|x| *x;

    let first_result = bf.first(f);
    let bimap_result = bf.bimap(f, id_b);

    let g: &dyn Fn(&i32) -> i32 = &|x| x * 2;
    let id_a: &dyn Fn(&i32) -> i32 = &|x| *x;

    let second_result = bf.second(g);
    let bimap_result2 = bf.bimap(id_a, g);

    first_result == bimap_result && second_result == bimap_result2
}

// Test the composition law: bimap(f . g, h . i) == bimap(f, h) . bimap(g, i)
#[quickcheck]
fn bifunctor_composition_law(bf: TestBifunctor<i32, i32>) -> bool {
    // Functions for the first type parameter
    let f1: &dyn Fn(&i32) -> i32 = &|x| x + 1;
    let f2: &dyn Fn(&i32) -> i32 = &|x| x * 2;

    // Functions for the second type parameter
    let g1: &dyn Fn(&i32) -> i32 = &|x| x - 1;
    let g2: &dyn Fn(&i32) -> i32 = &|x| x / 2;

    // Compose functions
    let f1_after_f2 = |x: &i32| f1(&f2(x));
    let g1_after_g2 = |x: &i32| g1(&g2(x));

    // Left side of the law: bimap(f1 ∘ f2, g1 ∘ g2)
    let left = bf.bimap(f1_after_f2, g1_after_g2);

    // Right side of the law: bimap(f1, g1) ∘ bimap(f2, g2)
    let inner = bf.bimap(f2, g2);
    let right = inner.bimap(f1, g1);

    left == right
}

// Test that bimap preserves the structure
#[quickcheck]
fn bifunctor_structure_preservation(bf: TestBifunctor<i32, i32>) -> bool {
    let f: &dyn Fn(&i32) -> String = &|x| x.to_string();
    let g: &dyn Fn(&i32) -> bool = &|x| *x > 0;

    let result = bf.bimap(f, g);

    // Check that the structure is preserved
    result.0 == bf.0.to_string() && result.1 == (bf.1 > 0)
}
