use std::sync::Arc;
use rustica::traits::category::Category;
use rustica::traits::composable::Composable;
use rustica::traits::hkt::AnyBox;
use super::TestFunctor;

#[test]
fn test_category_identity() {
    let test_functor = TestFunctor(42);
    
    // Left identity: id . f = f
    let id_morphism = TestFunctor::<i32>::identity_morphism();
    let result = test_functor.compose_morphism(&id_morphism);
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    assert_eq!(value, 42);
    
    // Right identity: f . id = f
    let result = test_functor.compose_morphism(&id_morphism);
    let value = result.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    assert_eq!(value, 42);
}

#[test]
fn test_category_associativity() {
    let test_functor = TestFunctor(0);
    
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
    
    let h = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val - 3) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // (f . g) . h = f . (g . h)
    let fg = test_functor.compose(f.clone(), g.clone());
    let gh = test_functor.compose(g, h.clone());
    
    let left = test_functor.compose_with(test_functor.compose(fg, h));
    let right = test_functor.compose_with(test_functor.compose(f, gh));
    
    let left_val = left.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    let right_val = right.downcast_ref::<TestFunctor<i32>>()
        .map(|f| f.0)
        .unwrap_or_default();
    
    assert_eq!(left_val, right_val);
}

#[test]
fn test_composable_operations() {
    let test_functor = TestFunctor(0);
    
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
    
    // Test composition
    let composed = test_functor.compose(f, g);
    let input = Arc::new(5) as AnyBox;
    let result = composed(input);
    
    let value = result.downcast_ref::<i32>()
        .map(|x| *x)
        .unwrap_or_default();
    assert_eq!(value, 11); // (5 * 2) + 1
}

#[test]
fn test_category_composition_chain() {
    let test_functor = TestFunctor(0);
    
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
    
    let h = Arc::new(|x: AnyBox| {
        if let Some(val) = x.downcast_ref::<i32>() {
            Arc::new(val - 3) as AnyBox
        } else {
            x
        }
    }) as Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
    
    // Chain multiple compositions
    let composed = test_functor.compose(f, test_functor.compose(g, h));
    let input = Arc::new(5) as AnyBox;
    let result = composed(input);
    
    let value = result.downcast_ref::<i32>()
        .map(|x| *x)
        .unwrap_or_default();
    assert_eq!(value, 8); // ((5 - 3) * 2) + 1
}
