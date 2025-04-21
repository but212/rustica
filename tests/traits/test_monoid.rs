extern crate quickcheck;
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use std::marker::PhantomData;

// Define a new TestMonoid type specifically for testing monoid properties
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestMonoid<A>(Vec<A>, PhantomData<A>);

impl<A: Clone> TestMonoid<A> {
    pub fn new(values: Vec<A>) -> Self {
        TestMonoid(values, PhantomData)
    }
}

// Implement Semigroup for TestMonoid
impl<A: Clone> Semigroup for TestMonoid<A> {
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.0.clone();
        result.extend(other.0.clone());
        TestMonoid(result, PhantomData)
    }

    fn combine_owned(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }
}

// Implement Monoid for TestMonoid
impl<A: Clone> Monoid for TestMonoid<A> {
    fn empty() -> Self {
        TestMonoid(Vec::new(), PhantomData)
    }
}

// Implement Arbitrary for TestMonoid<i32> for property-based testing
impl Arbitrary for TestMonoid<i32> {
    fn arbitrary(g: &mut Gen) -> Self {
        let size = u8::arbitrary(g) % 10;
        let mut v = Vec::with_capacity(size as usize);
        for _ in 0..size {
            v.push(i32::arbitrary(g));
        }
        TestMonoid::new(v)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let values = self.0.clone();
        Box::new(values.shrink().map(TestMonoid::new))
    }
}

// Implement Arbitrary for TestMonoid<String> for property-based testing
impl Arbitrary for TestMonoid<String> {
    fn arbitrary(g: &mut Gen) -> Self {
        let size = u8::arbitrary(g) % 5;
        let mut v = Vec::with_capacity(size as usize);
        for _ in 0..size {
            let len = u8::arbitrary(g) % 5 + 1;
            let s: String = (0..len)
                .map(|_| {
                    let c: char = (b'a' + (u8::arbitrary(g) % 26)) as char;
                    c
                })
                .collect();
            v.push(s);
        }
        TestMonoid::new(v)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let values = self.0.clone();
        Box::new(values.shrink().map(TestMonoid::new))
    }
}

// Test the left identity law: empty().combine(x) == x
#[quickcheck]
fn monoid_left_identity(x: TestMonoid<i32>) -> bool {
    TestMonoid::empty().combine(&x) == x
}

// Test the right identity law: x.combine(empty()) == x
#[quickcheck]
fn monoid_right_identity(x: TestMonoid<i32>) -> bool {
    x.combine(&TestMonoid::empty()) == x
}

// Test the associativity law required by Semigroup: (a.combine(b)).combine(c) == a.combine(b.combine(c))
#[quickcheck]
fn semigroup_associativity(a: TestMonoid<i32>, b: TestMonoid<i32>, c: TestMonoid<i32>) -> bool {
    let left = a.combine(&b).combine(&c);
    let right = a.combine(&b.combine(&c));
    left == right
}

// Test the owned version of the associativity law
#[quickcheck]
fn semigroup_associativity_owned(
    a: TestMonoid<i32>, b: TestMonoid<i32>, c: TestMonoid<i32>,
) -> bool {
    let left = a.clone().combine_owned(b.clone()).combine_owned(c.clone());
    let right = a.combine_owned(b.combine_owned(c));
    left == right
}

// Test string monoid
#[quickcheck]
fn string_monoid_laws(a: String, b: String, c: String) -> bool {
    // Identity laws
    let left_identity = String::empty().combine_owned(a.clone()) == a.clone();
    let right_identity = a.clone().combine_owned(String::empty()) == a;

    // Associativity law
    let assoc_left = a.clone().combine_owned(b.clone()).combine_owned(c.clone());
    let assoc_right = a.combine_owned(b.combine_owned(c));
    let associativity = assoc_left == assoc_right;

    left_identity && right_identity && associativity
}

// Test vec monoid
#[quickcheck]
fn vec_monoid_laws(a: Vec<i32>, b: Vec<i32>, c: Vec<i32>) -> bool {
    // Identity laws
    let left_identity = Vec::<i32>::empty().combine_owned(a.clone()) == a.clone();
    let right_identity = a.clone().combine_owned(Vec::<i32>::empty()) == a;

    // Associativity law
    let assoc_left = a.clone().combine_owned(b.clone()).combine_owned(c.clone());
    let assoc_right = a.combine_owned(b.combine_owned(c));
    let associativity = assoc_left == assoc_right;

    left_identity && right_identity && associativity
}

#[quickcheck]
fn test_combine_all_empty() -> bool {
    use rustica::traits::monoid::MonoidExt;
    let combined = TestMonoid::<i32>::combine_all(TestMonoid::empty(), std::iter::empty());
    combined == TestMonoid::empty()
}

#[quickcheck]
fn test_combine_all_single(first: TestMonoid<i32>) -> bool {
    use rustica::traits::monoid::MonoidExt;
    let combined = TestMonoid::combine_all(first.clone(), std::iter::empty());
    combined == first
}

#[quickcheck]
fn test_combine_all_multiple(first: TestMonoid<i32>, second: TestMonoid<i32>) -> bool {
    use rustica::traits::monoid::MonoidExt;
    let rest = vec![second.clone()];
    let combined = TestMonoid::combine_all(first.clone(), rest.into_iter());
    let expected = first.combine(&second);
    combined == expected
}

#[quickcheck]
fn test_is_empty_monoid(x: TestMonoid<i32>) -> bool {
    use rustica::traits::monoid::MonoidExt;
    let empty = TestMonoid::<i32>::empty();
    empty.is_empty_monoid() && (x.is_empty_monoid() == (x == empty))
}

#[quickcheck]
fn test_repeat(x: TestMonoid<i32>, n: u8) -> bool {
    use rustica::traits::monoid::repeat;
    let n = (n % 10) as usize; // Limit to reasonable size

    let repeated = repeat(x.clone(), n);

    if n == 0 {
        repeated == TestMonoid::empty()
    } else {
        let mut expected = x.clone();
        for _ in 1..n {
            expected = expected.combine(&x);
        }
        repeated == expected
    }
}

#[quickcheck]
fn test_mconcat(xs: Vec<TestMonoid<i32>>) -> bool {
    use rustica::traits::monoid::mconcat;

    let result = mconcat(&xs);

    if xs.is_empty() {
        result == TestMonoid::empty()
    } else {
        let mut expected = xs[0].clone();
        for x in &xs[1..] {
            expected = expected.combine(x);
        }
        result == expected
    }
}

#[quickcheck]
fn test_power(base: TestMonoid<i32>, n: u8) -> bool {
    use rustica::traits::monoid::power;
    let n = (n % 10) as usize; // Limit to reasonable size

    let result = power(base.clone(), n);

    if n == 0 {
        result == TestMonoid::empty()
    } else if n == 1 {
        result == base
    } else {
        let mut expected = base.clone();
        for _ in 1..n {
            expected = expected.combine(&base);
        }
        result == expected
    }
}
