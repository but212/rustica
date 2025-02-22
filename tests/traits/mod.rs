pub mod functor;
pub mod monad;
pub mod applicative;
pub mod category;

use std::sync::Arc;
use quickcheck::{Arbitrary, Gen};
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::hkt::{HKT, TypeOps, AnyBox};
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use rustica::traits::category::Category;
use rustica::traits::arrow::Arrow;
use rustica::traits::composable::Composable;

// Test data structures
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TestFunctor<T: TypeOps + Default + Eq + Clone + 'static>(pub T);

impl<T: TypeOps + Default + Eq + Clone + 'static> HKT for TestFunctor<T> {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.0.clone()) as AnyBox
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        if let Some(value) = boxed.downcast_ref::<T>() {
            Some(Arc::new(TestFunctor(value.clone())) as AnyBox)
        } else {
            None
        }
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Identity for TestFunctor<T> {
    fn identity() -> AnyBox {
        Arc::new(TestFunctor(T::default())) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(TestFunctor(T::default())) as AnyBox)
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Functor for TestFunctor<T> {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(self.0.clone()) as AnyBox)
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Pure for TestFunctor<T> {
    fn pure(value: AnyBox) -> AnyBox {
        if let Some(val) = value.downcast_ref::<T>() {
            Arc::new(TestFunctor(val.clone())) as AnyBox
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Applicative for TestFunctor<T> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(self.0.clone()) as AnyBox)
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(b_functor) = b.downcast_ref::<TestFunctor<T>>() {
            let result = f(Arc::new(self.0.clone()) as AnyBox, Arc::new(b_functor.0.clone()) as AnyBox);
            if let Some(val) = result.downcast_ref::<T>() {
                Arc::new(TestFunctor(val.clone())) as AnyBox
            } else {
                Arc::new(TestFunctor(T::default())) as AnyBox
            }
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(b_functor), Some(c_functor)) = (b.downcast_ref::<TestFunctor<T>>(), c.downcast_ref::<TestFunctor<T>>()) {
            let result = f(
                Arc::new(self.0.clone()) as AnyBox,
                Arc::new(b_functor.0.clone()) as AnyBox,
                Arc::new(c_functor.0.clone()) as AnyBox
            );
            if let Some(val) = result.downcast_ref::<T>() {
                Arc::new(TestFunctor(val.clone())) as AnyBox
            } else {
                Arc::new(TestFunctor(T::default())) as AnyBox
            }
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Monad for TestFunctor<T> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(self.0.clone()) as AnyBox)
    }

    fn join(&self) -> AnyBox {
        let inner_box = Arc::new(self.0.clone()) as AnyBox;
        if let Some(inner) = self.downcast(&inner_box) {
            inner
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Category for TestFunctor<T> {
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(func) = other.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            func(Arc::new(self.0.clone()) as AnyBox)
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(TestFunctor(T::default())) as AnyBox
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Composable for TestFunctor<T> {
    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(self.0.clone()) as AnyBox)
    }
}

impl<T: TypeOps + Default + Eq + Clone + 'static> Arrow for TestFunctor<T> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            func(Arc::new(self.0.clone()) as AnyBox)
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let val = Arc::new(self.0.clone()) as AnyBox;
            Arc::new((func(val.clone()), val)) as AnyBox
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let val = Arc::new(self.0.clone()) as AnyBox;
            Arc::new((val.clone(), func(val))) as AnyBox
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        let f_val = if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            func(Arc::new(self.0.clone()) as AnyBox)
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        };
        
        let g_val = if let Some(func) = g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            func(Arc::new(self.0.clone()) as AnyBox)
        } else {
            Arc::new(TestFunctor(T::default())) as AnyBox
        };

        Arc::new((f_val, g_val)) as AnyBox
    }
}

impl<T: TypeOps + Default + Eq + Clone + Arbitrary + 'static> Arbitrary for TestFunctor<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let value = T::arbitrary(g);
        TestFunctor(value)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(std::iter::empty())
    }
}