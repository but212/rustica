use std::sync::Arc;
use rustica::datatypes::cont::Cont;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use rustica::traits::hkt::AnyBox;

#[test]
fn test_cont_left_identity() {
    let x = Arc::new(42) as AnyBox;
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(Cont::<i32, i32>::pure(Arc::new(*val + 1) as AnyBox)) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Left identity: return a >>= f = f a
    let cont = Cont::<i32, i32>::pure(x.clone());
    let cont_result = cont.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast cont")
        .bind(f.clone());
    
    let result = cont_result.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast result")
        .run(Arc::new(|x| x));
    
    let f_result = f(x);
    let f_cont = f_result.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast f result");
    let f_value = f_cont.run(Arc::new(|x| x));
    
    assert_eq!(result, f_value);
}

#[test]
fn test_cont_right_identity() {
    let x = Arc::new(42) as AnyBox;
    let cont = Cont::<i32, i32>::pure(x);
    
    // Right identity: m >>= return = m
    let cont_result = cont.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast cont")
        .bind(Arc::new(|x| Arc::new(Cont::<i32, i32>::pure(x)) as AnyBox));
    
    let result = cont_result.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast result")
        .run(Arc::new(|x| x));
    
    let original_result = cont.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast original cont")
        .run(Arc::new(|x| x));
    
    assert_eq!(result, original_result);
}

#[test]
fn test_cont_associativity() {
    let x = Arc::new(42) as AnyBox;
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(Cont::<i32, i32>::pure(Arc::new(*val + 1) as AnyBox)) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let g = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(Cont::<i32, i32>::pure(Arc::new(*val * 2) as AnyBox)) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
    let cont = Cont::<i32, i32>::pure(x);
    let cont_ref = cont.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast cont");
    
    let left = cont_ref.bind(f.clone())
        .downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast first bind")
        .bind(g.clone());
    
    let right = cont_ref.bind(Arc::new(move |x| {
        let fx = f(x);
        fx.downcast_ref::<Cont<i32, i32>>()
            .expect("Failed to downcast f(x)")
            .bind(g.clone())
    }));
    
    let left_result = left.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast left result")
        .run(Arc::new(|x| x));
    
    let right_result = right.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast right result")
        .run(Arc::new(|x| x));
    
    assert_eq!(left_result, right_result);
}

#[test]
fn test_cont_composition() {
    let x = Arc::new(42) as AnyBox;
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(Cont::<i32, i32>::pure(Arc::new(*val + 1) as AnyBox)) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let g = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(Cont::<i32, i32>::pure(Arc::new(*val * 2) as AnyBox)) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let cont = Cont::<i32, i32>::pure(x);
    let cont_ref = cont.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast cont");
    
    let composed = cont_ref.bind(f.clone())
        .downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast first bind")
        .bind(g.clone());
    
    let result = composed.downcast_ref::<Cont<i32, i32>>()
        .expect("Failed to downcast result")
        .run(Arc::new(|x| x));
    
    assert_eq!(result, 86); // (42 + 1) * 2
}
