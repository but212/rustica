use quickcheck_macros::quickcheck;
use rustica::traits::bifunctor::Bifunctor;
use rustica::datatypes::choice::Choice;
use rustica::fntype::{FnType, FnTrait};

#[quickcheck]
fn bifunctor_identity(x: i32, y: i32) -> bool {
    let choice = Choice::Both(x, y);
    let id = FnType::new(|x| x);
    choice.clone().bimap(id.clone(), id) == choice
}

#[quickcheck]
fn bifunctor_composition(x: i32, y: i32) -> bool {
    let choice = Choice::Both(x, y);
    let f1 = FnType::new(|x: i32| x.saturating_add(1));
    let f2 = FnType::new(|x: i32| x.saturating_mul(2));
    let g1 = FnType::new(|x: i32| x.saturating_sub(3));
    let g2 = FnType::new(|x: i32| x.saturating_div(4));
    
    let left = choice.clone()
        .bimap(f1.clone(), g1.clone())
        .bimap(f2.clone(), g2.clone());
    
    let right = choice.bimap(
        FnType::new(move |x| f2.call(f1.call(x))),
        FnType::new(move |x| g2.call(g1.call(x)))
    );
    
    left == right
}