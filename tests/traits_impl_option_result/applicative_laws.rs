use quickcheck_macros::quickcheck;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::pure::Pure;

// --- Option Applicative Laws ---

#[quickcheck]
fn qc_option_applicative_laws(v: Option<i32>, x: i32, u_some: bool) -> bool {
    let f: fn(&i32) -> i32 = |n| n.saturating_add(1);
    let id: fn(&i32) -> i32 = |t| *t;

    let pure_f = Option::<fn(&i32) -> i32>::pure(&f);
    let pure_x = Option::<i32>::pure(&x);
    let u: Option<fn(&i32) -> i32> = if u_some { Some(f) } else { None };

    // 1. Identity: pure(id) <*> v == v
    let identity = Applicative::apply(&Option::<fn(&i32) -> i32>::pure(&id), &v) == v;

    // 2. Homomorphism: pure(f) <*> pure(x) == pure(f(x))
    let homomorphism = Applicative::apply(&pure_f, &pure_x) == Option::<i32>::pure(&f(&x));

    // 3. Interchange: u <*> pure(x) == pure(|f| f(x)) <*> u
    let interchange =
        Applicative::apply(&u, &pure_x) == Option::<i32>::lift2(|f, x| f(x), &u, &pure_x);

    // 4. Functor Relationship: fmap(f, v) == pure(f) <*> v
    let functor_rel = v.fmap(f) == Applicative::apply(&pure_f, &v);

    identity && homomorphism && interchange && functor_rel
}

// --- Result Applicative Laws ---

#[quickcheck]
fn qc_result_applicative_laws(v: Result<i32, i8>, x: i32, is_ok: bool, err: i8) -> bool {
    let f: fn(&i32) -> i32 = |n| n.saturating_add(1);
    let id: fn(&i32) -> i32 = |t| *t;

    let pure_f = Result::<fn(&i32) -> i32, i8>::pure(&f);
    let pure_x = Result::<i32, i8>::pure(&x);
    let u: Result<fn(&i32) -> i32, i8> = if is_ok { Ok(f) } else { Err(err) };

    // 1. Identity
    let identity = Applicative::apply(&Result::<fn(&i32) -> i32, i8>::pure(&id), &v) == v;

    // 2. Homomorphism
    let homomorphism = Applicative::apply(&pure_f, &pure_x) == Result::<i32, i8>::pure(&f(&x));

    // 3. Interchange
    let interchange =
        Applicative::apply(&u, &pure_x) == Result::<i32, i8>::lift2(|f, x| f(x), &u, &pure_x);

    identity && homomorphism && interchange
}

// --- Vec Applicative Laws ---

#[quickcheck]
fn qc_vec_applicative_laws(v: Vec<i32>, x: i32) -> bool {
    let f: fn(&i32) -> i32 = |n| n.saturating_add(1);
    let id: fn(&i32) -> i32 = |t| *t;

    // 1. Identity
    let identity = Applicative::apply(&Vec::<fn(&i32) -> i32>::pure(&id), &v) == v;

    // 2. Homomorphism
    let pure_f = Vec::<fn(&i32) -> i32>::pure(&f);
    let pure_x = Vec::<i32>::pure(&x);
    let homomorphism = Applicative::apply(&pure_f, &pure_x) == Vec::<i32>::pure(&f(&x));

    identity && homomorphism
}

// --- Composition Law (Tested separately due to complexity) ---

#[quickcheck]
fn qc_standard_composition_law(w_opt: Option<i32>, w_res: Result<i32, i8>) -> bool {
    let f: fn(&i32) -> i32 = |x| x.saturating_add(1);
    let g: fn(&i32) -> i32 = |x| x.saturating_mul(2);

    let u_opt = Some(f);
    let v_opt = Some(g);
    let u_res: Result<_, i8> = Ok(f);
    let v_res: Result<_, i8> = Ok(g);

    // pure(compose) <*> u <*> v <*> w == u <*> (v <*> w)
    let left_opt = Option::<i32>::lift3(|f, g, x| f(&g(x)), &u_opt, &v_opt, &w_opt);
    let right_opt = Applicative::apply(&u_opt, &Applicative::apply(&v_opt, &w_opt));

    let left_res = Result::<i32, i8>::lift3(|f, g, x| f(&g(x)), &u_res, &v_res, &w_res);
    let right_res = Applicative::apply(&u_res, &Applicative::apply(&v_res, &w_res));

    left_opt == right_opt && left_res == right_res
}
