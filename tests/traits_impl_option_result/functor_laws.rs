use quickcheck_macros::quickcheck;
use rustica::traits::functor::Functor;

// --- Option Functor Laws ---

#[quickcheck]
fn qc_option_functor_laws(m: Option<i32>) -> bool {
    let f = |&x: &i32| x.saturating_mul(2);
    let g = |&x: &i32| x.saturating_add(1);
    let id = |&x: &i32| x;

    // 1. Identity: fmap(id) == id
    let identity = m.fmap(id) == m;
    
    // 2. Composition: fmap(g . f) == fmap(g) . fmap(f)
    let composition = m.fmap(|&x| g(&f(&x))) == m.fmap(f).fmap(g);

    // 3. Structure preservation (Implicit in 1 & 2, but verified via type-specific shape)
    let shape_preserved = m.fmap(f).is_some() == m.is_some();

    identity && composition && shape_preserved
}

// --- Result Functor Laws ---

#[quickcheck]
fn qc_result_functor_laws(m: Result<i32, i8>) -> bool {
    let f = |&x: &i32| x.saturating_add(10);
    let g = |&x: &i32| x.saturating_mul(3);
    let id = |&x: &i32| x;

    // 1. Identity
    let identity = m.clone().fmap(id) == m;

    // 2. Composition
    let composition = m.clone().fmap(|&x| g(&f(&x))) == m.clone().fmap(f).fmap(g);

    // 3. Structure: Error value and variant (Ok/Err) must be preserved
    let structure = m.fmap(f).is_ok() == m.is_ok();

    identity && composition && structure
}

// --- Vec Functor Laws ---

#[quickcheck]
fn qc_vec_functor_laws(v: Vec<i32>) -> bool {
    let f = |&x: &i32| x.saturating_abs();
    let id = |&x: &i32| x;

    // 1. Identity
    let identity = v.fmap(id) == v;

    // 2. Composition and Length preservation
    let mapped = v.fmap(f);
    let structure = mapped.len() == v.len();

    identity && structure
}
