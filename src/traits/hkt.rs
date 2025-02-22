use std::any::Any;
use std::sync::Arc;
use std::collections::HashMap;
use std::hash::Hash;

pub type AnyBox = Arc<dyn Any + Send + Sync>;

/// Object-safe trait for type operations.
///
/// This trait provides methods for cloning and equality checking
/// that work with dynamically typed objects.
pub trait TypeOps: Any + Send + Sync {
    /// Creates a boxed clone of self.
    ///
    /// # Returns
    /// An `AnyBox` containing a clone of the implementing type.
    fn clone_box(&self) -> AnyBox;
    
    /// Checks if self equals another value.
    ///
    /// # Arguments
    /// * `other` - An `AnyBox` to compare against.
    ///
    /// # Returns
    /// `true` if the values are equal, `false` otherwise.
    fn equals(&self, other: &AnyBox) -> bool;
}

/// Implements TypeOps for common types.
impl<T> TypeOps for T 
where 
    T: Clone + PartialEq + Send + Sync + 'static 
{
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn equals(&self, other: &AnyBox) -> bool {
        other.downcast_ref::<T>()
            .map_or(false, |other| self == other)
    }
}

/// Object-safe higher-kinded type operations.
///
/// This trait provides methods for type-level operations
/// that can be performed on boxed values.
pub trait HKT: Send + Sync {
    /// Transforms this value into a boxed type.
    ///
    /// # Returns
    /// An `AnyBox` containing the transformed value.
    fn apply_type(&self) -> AnyBox;

    /// Attempts to downcast a boxed value.
    ///
    /// # Arguments
    /// * `boxed` - An `AnyBox` to attempt to downcast.
    ///
    /// # Returns
    /// `Some(AnyBox)` if the downcast was successful, `None` otherwise.
    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox>;
}

impl HKT for String {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<String>()
            .map(|s| Arc::new(s.clone()) as AnyBox)
    }
}

impl HKT for bool {
    fn apply_type(&self) -> AnyBox {
        Arc::new(*self)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<bool>()
            .map(|b| Arc::new(*b) as AnyBox)
    }
}

impl HKT for i32 {
    fn apply_type(&self) -> AnyBox {
        Arc::new(*self)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<i32>()
            .map(|n| Arc::new(*n) as AnyBox)
    }
}

impl HKT for i64 {
    fn apply_type(&self) -> AnyBox {
        Arc::new(*self)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<i64>()
            .map(|n| Arc::new(*n) as AnyBox)
    }
}

impl HKT for f32 {
    fn apply_type(&self) -> AnyBox {
        Arc::new(*self)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<f32>()
            .map(|n| Arc::new(*n) as AnyBox)
    }
}

impl HKT for f64 {
    fn apply_type(&self) -> AnyBox {
        Arc::new(*self)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<f64>()
            .map(|n| Arc::new(*n) as AnyBox)
    }
}

impl<T> HKT for Option<T>
where
    T: TypeOps + 'static
{
    fn apply_type(&self) -> AnyBox {
        match self {
            Some(x) => Arc::new(Some(x.clone_box())),
            None => Arc::new(None::<AnyBox>),
        }
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Option<AnyBox>>()
            .map(|opt| Arc::new(opt.clone()) as AnyBox)
    }
}

impl<T> HKT for Vec<T>
where
    T: TypeOps + 'static
{
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.iter().map(|x| x.clone_box()).collect::<Vec<_>>())
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Vec<AnyBox>>()
            .map(|v| Arc::new(v.clone()) as AnyBox)
    }
}

impl<T, E> HKT for Result<T, E>
where
    T: TypeOps + 'static,
    E: TypeOps + 'static
{
    fn apply_type(&self) -> AnyBox {
        match self {
            Ok(x) => Arc::new(Ok::<AnyBox, AnyBox>(x.clone_box())),
            Err(e) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box())),
        }
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Result<AnyBox, AnyBox>>()
            .map(|r| Arc::new(r.clone()) as AnyBox)
    }
}

impl<K, V> HKT for HashMap<K, V>
where
    K: TypeOps + Clone + Hash + Eq + 'static,
    V: TypeOps + 'static
{
    fn apply_type(&self) -> AnyBox {
        let mut result = HashMap::<std::any::TypeId, AnyBox>::new();
        for (_, v) in self {
            result.insert(std::any::TypeId::of::<V>(), v.clone_box());
        }
        Arc::new(result)
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<HashMap<std::any::TypeId, AnyBox>>()
            .map(|h| Arc::new(h.clone()) as AnyBox)
    }
}
