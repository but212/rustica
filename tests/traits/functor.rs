use std::sync::Arc;
use rustica::traits::functor::Functor;
use rustica::traits::hkt::AnyBox;
use super::TestFunctor;

#[test]
fn test_functor_identity() {
    let x = TestFunctor(42);
    let id = Arc::new(|x: AnyBox| x) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let result = x.fmap(id);
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    
    assert_eq!(value, 42);
}

#[test]
fn test_functor_composition() {
    let x = TestFunctor(42);
    
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let g = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val * 2) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Test composition: fmap (f . g) = fmap f . fmap g
    let f_clone = Arc::clone(&f);
    let g_clone = Arc::clone(&g);
    let compose = Arc::new(move |x: AnyBox| {
        let f = Arc::clone(&f_clone);
        let g = Arc::clone(&g_clone);
        f(g(x))
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let left = x.fmap(compose);
    let right = x.fmap(Arc::clone(&g)).downcast_ref::<TestFunctor<i32>>()
        .map(|tf| tf.fmap(Arc::clone(&f)))
        .unwrap_or_else(|| Arc::new(TestFunctor(0)) as AnyBox);
    
    let left_val = left.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    let right_val = right.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    
    assert_eq!(left_val, right_val);
}

#[test]
fn test_functor_preservation() {
    let x = TestFunctor(42);
    let y = TestFunctor(7);
    
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let result_x = x.fmap(f.clone());
    let result_y = y.fmap(f);
    
    let x_val = result_x.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    let y_val = result_y.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    
    assert_eq!(x_val, 43);
    assert_eq!(y_val, 8);
}

#[test]
fn test_functor_structure() {
    let inner = TestFunctor(42);
    let x = TestFunctor(inner);
    
    let f = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val + 1) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let g = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val * 2) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    let result = x.fmap(f.clone()).downcast_ref::<TestFunctor<TestFunctor<i32>>>()
        .map(|outer| {
            let inner = outer.0.clone();
            inner.fmap(g)
        })
        .unwrap_or_else(|| Arc::new(TestFunctor(0)) as AnyBox);
    
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    
    assert_eq!(value, 86); // (42 + 1) * 2
}
