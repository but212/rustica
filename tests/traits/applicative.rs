use std::sync::Arc;
use rustica::traits::applicative::Applicative;
use rustica::traits::pure::Pure;
use rustica::traits::hkt::AnyBox;
use super::TestFunctor;

#[test]
fn test_applicative_identity() {
    let v = TestFunctor(42);
    let id_fn = Arc::new(|x: AnyBox| x) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    let pure_id = TestFunctor::pure(Arc::new(id_fn.clone()) as AnyBox);
    
    // Identity: pure id <*> v = v
    let result = if let Some(f) = pure_id.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(id_fn.clone())
    } else {
        panic!("Failed to downcast pure_id")
    };
    
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast result");
    
    assert_eq!(value, 42);
}

#[test]
fn test_applicative_homomorphism() {
    let x = 42;
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Homomorphism: pure f <*> pure x = pure (f x)
    let pure_f = TestFunctor::pure(Arc::new(f.clone()) as AnyBox);
    let pure_x = TestFunctor::pure(Arc::new(x) as AnyBox);
    
    let left = if let Some(f_ref) = pure_f.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f_ref.apply(f.clone())
    } else {
        panic!("Failed to downcast pure_f")
    };
    
    let right = TestFunctor::pure(f(Arc::new(x) as AnyBox));
    
    let left_val = left.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast left");
    let right_val = right.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast right");
    
    assert_eq!(left_val, right_val);
}

#[test]
fn test_applicative_interchange() {
    let x = 42;
    let u = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Interchange: u <*> pure y = pure ($ y) <*> u
    let pure_u = TestFunctor::pure(Arc::new(u.clone()) as AnyBox);
    let pure_x = TestFunctor::pure(Arc::new(x) as AnyBox);
    
    let left = if let Some(f) = pure_u.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(u.clone())
    } else {
        panic!("Failed to downcast pure_u")
    };
    
    let apply_y = Arc::new(move |f: AnyBox| {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            func(Arc::new(x) as AnyBox)
        } else {
            f
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let pure_apply_y = TestFunctor::pure(Arc::new(apply_y.clone()) as AnyBox);
    let right = if let Some(f) = pure_apply_y.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(u.clone())
    } else {
        panic!("Failed to downcast pure_apply_y")
    };
    
    let left_val = left.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast left");
    let right_val = right.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast right");
    
    assert_eq!(left_val, right_val);
}

#[test]
fn test_applicative_composition() {
    let x = 42;
    
    let u = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val * 2) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let v = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let w = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val * 3) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    let pure_x = TestFunctor::pure(Arc::new(x) as AnyBox);
    let pure_u = TestFunctor::pure(Arc::new(u.clone()) as AnyBox);
    let pure_v = TestFunctor::pure(Arc::new(v.clone()) as AnyBox);
    let pure_w = TestFunctor::pure(Arc::new(w.clone()) as AnyBox);
    
    // Left side: u <*> (v <*> w)
    let vw = if let Some(f) = pure_v.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(w.clone())
    } else {
        panic!("Failed to downcast pure_v")
    };
    
    let left = if let Some(f) = pure_u.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(vw)
    } else {
        panic!("Failed to downcast pure_u")
    };
    
    // Right side: pure (.) <*> u <*> v <*> w
    let compose = Arc::new(|f: AnyBox| {
        if let Some(f1) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            Arc::new(move |g: AnyBox| {
                if let Some(f2) = g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                    Arc::new(move |x: AnyBox| f1(f2(x))) as AnyBox
                } else {
                    g
                }
            }) as AnyBox
        } else {
            f
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let pure_compose = TestFunctor::pure(Arc::new(compose.clone()) as AnyBox);
    let step1 = if let Some(f) = pure_compose.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(u.clone())
    } else {
        panic!("Failed to downcast pure_compose")
    };
    
    let step2 = if let Some(f) = step1.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(v.clone())
    } else {
        panic!("Failed to downcast step1")
    };
    
    let right = if let Some(f) = step2.downcast_ref::<TestFunctor<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>>() {
        f.apply(w.clone())
    } else {
        panic!("Failed to downcast step2")
    };
    
    let left_val = left.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast left");
    let right_val = right.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast right");
    
    assert_eq!(left_val, right_val);
}

#[test]
fn test_applicative_lift() {
    let x = 42;
    let y = 7;
    let z = 3;
    
    let pure_x = TestFunctor::pure(Arc::new(x) as AnyBox);
    let pure_y = TestFunctor::pure(Arc::new(y) as AnyBox);
    let pure_z = TestFunctor::pure(Arc::new(z) as AnyBox);
    
    let result = TestFunctor::lift3(
        &TestFunctor::pure(Arc::new(x) as AnyBox),
        pure_y,
        pure_z,
        Arc::new(|x: AnyBox, y: AnyBox, z: AnyBox| {
            let x = x.downcast_ref::<i32>().expect("Failed to downcast x").clone();
            let y = y.downcast_ref::<i32>().expect("Failed to downcast y").clone();
            let z = z.downcast_ref::<i32>().expect("Failed to downcast z").clone();
            Arc::new(x + y + z) as AnyBox
        }) as Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>
    );
    
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .expect("Failed to downcast result");
    
    assert_eq!(value, 52); // 42 + 7 + 3
}
