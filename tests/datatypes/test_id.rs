use rustica::datatypes::id::Id;
use rustica::traits::{applicative::Applicative, functor::Functor, monad::Monad, pure::Pure};

#[test]
fn test_id_monadic_laws() {
    let x = Id::new(42);
    let f = |n: &i32| Id::new(n * 2);
    let g = |n: &i32| Id::new(n + 3);

    assert_eq!(x.clone().fmap(|n| *n).unwrap(), x.unwrap());
    assert_eq!(
        x.clone().fmap(|n| n + 3).fmap(|n| n * 2).unwrap(),
        x.clone().fmap(|n| (n + 3) * 2).unwrap()
    );
    let app_f = Id::new(|n: &i32| n + 1);
    assert_eq!(app_f.apply(&x).unwrap(), 43);
    assert_eq!(Id::<i32>::lift2(|a, b| a + b, &x, &Id::new(8)).unwrap(), 50);
    assert_eq!(Id::<i32>::pure(&42).bind(&f).unwrap(), f(&42).unwrap());
    assert_eq!(x.clone().bind(Id::<i32>::pure).unwrap(), x.unwrap());
    assert_eq!(
        x.clone().bind(f).bind(g).unwrap(),
        x.clone().bind(|n| f(n).bind(&g)).unwrap()
    );
    assert_eq!(Id::new(Id::new(100)).join::<i32>().unwrap(), 100);
}
