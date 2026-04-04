use quickcheck_macros::quickcheck;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

// --- Option Monad Laws ---

#[quickcheck]
fn qc_option_monad_laws(m: Option<i32>, val: i32) -> bool {
    let f = |&x: &i32| {
        if x > 0 {
            Some(x.saturating_mul(2))
        } else {
            None
        }
    };
    let g = |&x: &i32| Some(x.saturating_add(10));

    // 1. Left Identity: pure(val) >>= f == f(val)
    let left_id = Option::<i32>::pure(&val).bind(f) == f(&val);

    // 2. Right Identity: m >>= pure == m
    let right_id = m.clone().bind(Option::<i32>::pure) == m;

    // 3. Associativity: (m >>= f) >>= g == m >>= (\x -> f(x) >>= g)
    let assoc = m.clone().bind(f).bind(g) == m.clone().bind(|&x| f(&x).bind(g));

    // 4. Join Consistency: join(fmap(f, m)) == bind(m, f)
    let join_consist = m.fmap(f).join() == m.bind(f);

    left_id && right_id && assoc && join_consist
}

// --- Result Monad Laws ---

#[quickcheck]
fn qc_result_monad_laws(m: Result<i32, i8>, val: i32) -> bool {
    let f = |&x: &i32| -> Result<i32, i8> { Ok(x.saturating_mul(2)) };
    let g = |&x: &i32| -> Result<i32, i8> { Ok(x.saturating_add(10)) };

    // 1. Left Identity
    let left_id = Result::<i32, i8>::pure(&val).bind(f) == f(&val);

    // 2. Right Identity
    let right_id = m.clone().bind(Result::<i32, i8>::pure) == m;

    // 3. Associativity
    let assoc = m.clone().bind(f).bind(g) == m.clone().bind(|&x| f(&x).bind(g));

    // 4. Join Consistency
    let join_consist = m.fmap(f).join() == m.bind(f);

    left_id && right_id && assoc && join_consist
}

#[test]
fn test_monad_join_edge_cases() {
    // Specifically test join on nested structures which is hard to express in simple QuickCheck
    let nested_some: Option<Option<i32>> = Some(Some(42));
    assert_eq!(nested_some.join(), Some(42));

    let nested_err: Result<Result<i32, &str>, &str> = Ok(Err("inner"));
    assert_eq!(nested_err.join(), Err("inner"));
}
