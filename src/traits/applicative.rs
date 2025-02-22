use std::sync::Arc;
use crate::traits::hkt::{TypeOps, AnyBox};

/// The Applicative trait represents functors that support function application.
///
/// Applicative functors are more powerful than regular functors but less powerful than monads.
/// They allow function application through the functor context.
///
/// # Laws
///
/// 1. Identity:     `pure id <*> v = v`
/// 2. Composition:  `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
/// 3. Homomorphism: `pure f <*> pure x = pure (f x)`
/// 4. Interchange:  `u <*> pure y = pure ($ y) <*> u`
///
/// where `id` is the identity function and `(.)` is function composition.
///
/// # Example
///
/// ```rust
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use std::sync::Arc;
///
/// // Implementation for Option as an example
/// let x = Some(2);
/// let f = Some(|x| x + 1);
/// assert_eq!(x.apply(f), Some(3));
/// ```
pub trait Applicative {
    /// Applies a function wrapped in an applicative context to a value in an applicative context.
    ///
    /// # Arguments
    ///
    /// * `f` - A function wrapped in the applicative context
    ///
    /// # Returns
    ///
    /// The result of applying the function to the value, wrapped in the applicative context.
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Lifts a binary function to actions.
    ///
    /// This is a convenience method that helps in applying a binary function to
    /// two values in applicative contexts.
    ///
    /// # Arguments
    ///
    /// * `b` - The second argument in an applicative context
    /// * `f` - The binary function to lift
    ///
    /// # Returns
    ///
    /// The result of applying the binary function to both values, wrapped in the applicative context.
    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Lifts a ternary function to actions.
    ///
    /// Similar to `lift2`, but for functions taking three arguments.
    ///
    /// # Arguments
    ///
    /// * `b` - The second argument in an applicative context
    /// * `c` - The third argument in an applicative context
    /// * `f` - The ternary function to lift
    ///
    /// # Returns
    ///
    /// The result of applying the ternary function to all three values, wrapped in the applicative context.
    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;
}

impl<T> Applicative for Vec<T>
where
    T: TypeOps + 'static
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        for x in self.iter() {
            result.push(f(x.clone_box()));
        }
        Arc::new(result) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        if let Some(b_vec) = b.downcast_ref::<Vec<T>>() {
            for x in self.iter() {
                for y in b_vec.iter() {
                    result.push(f(x.clone_box(), y.clone_box()));
                }
            }
        }
        Arc::new(result) as AnyBox
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        if let (Some(b_vec), Some(c_vec)) = (b.downcast_ref::<Vec<T>>(), c.downcast_ref::<Vec<T>>()) {
            for x in self.iter() {
                for y in b_vec.iter() {
                    for z in c_vec.iter() {
                        result.push(f(x.clone_box(), y.clone_box(), z.clone_box()));
                    }
                }
            }
        }
        Arc::new(result) as AnyBox
    }
}

impl<T> Applicative for Option<T>
where
    T: TypeOps + 'static
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => f(x.clone_box()),
            None => Arc::new(None::<T>) as AnyBox
        }
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Option<T>>()) {
            (Some(x), Some(Some(y))) => f(x.clone_box(), y.clone_box()),
            _ => Arc::new(None::<T>) as AnyBox
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Option<T>>(), c.downcast_ref::<Option<T>>()) {
            (Some(x), Some(Some(y)), Some(Some(z))) => f(x.clone_box(), y.clone_box(), z.clone_box()),
            _ => Arc::new(None::<T>) as AnyBox
        }
    }
}

impl<K, V> Applicative for Result<K, V>
where
    K: TypeOps + 'static,
    V: TypeOps + Clone + 'static
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => f(x.clone_box()),
            Err(e) => Arc::new(Err::<K, V>(e.clone())) as AnyBox
        }
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Result<AnyBox, AnyBox>>()) {
            (Ok(x), Some(Ok(y))) => f(x.clone_box(), y.clone()),
            (Err(e), _) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box())),
            (_, Some(Err(e))) => Arc::new(Err::<AnyBox, AnyBox>(e.clone())),
            _ => Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Result<AnyBox, AnyBox>>(), c.downcast_ref::<Result<AnyBox, AnyBox>>()) {
            (Ok(x), Some(Ok(y)), Some(Ok(z))) => f(x.clone_box(), y.clone(), z.clone()),
            (Err(e), _, _) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box())),
            (_, Some(Err(e)), _) => Arc::new(Err::<AnyBox, AnyBox>(e.clone())),
            (_, _, Some(Err(e))) => Arc::new(Err::<AnyBox, AnyBox>(e.clone())),
            _ => Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
        }
    }
}