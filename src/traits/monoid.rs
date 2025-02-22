use crate::traits::hkt::{TypeOps, AnyBox};
use crate::traits::semigroup::Semigroup;
use std::sync::Arc;

/// A trait for monoids, which are semigroups with an identity element.
/// 
/// Monoids extend semigroups by introducing an identity element, often called
/// the "empty" element. This element, when combined with any other element,
/// leaves that element unchanged.
/// 
/// # Laws
/// 
/// A Monoid instance must satisfy these laws:
/// 
/// 1. Left Identity: For any value `x`,
///    `empty().combine(x) == x`
/// 2. Right Identity: For any value `x`,
///    `x.combine(empty()) == x`
/// 3. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) == (x.combine(y)).combine(z)`
/// 
/// # Relationship with Semigroup
/// 
/// Every Monoid is a Semigroup, but not every Semigroup is a Monoid.
/// The Monoid trait extends Semigroup by adding the `empty()` method.
pub trait Monoid: Semigroup {
    /// Returns the identity element of the monoid.
    ///
    /// The identity element is a value that, when combined with any other element,
    /// leaves that element unchanged.
    ///
    /// # Returns
    /// 
    /// An `AnyBox` containing the identity element of the monoid.
    fn empty(&self) -> AnyBox;
}

impl<T> Monoid for Vec<T>
where
    T: TypeOps + Clone + 'static
{
    fn empty(&self) -> AnyBox {
        Arc::new(Vec::<T>::new())
    }
}

impl Monoid for String {
    fn empty(&self) -> AnyBox {
        Arc::new(String::new())
    }
}

impl<T> Monoid for Option<T>
where
    T: TypeOps + 'static
{
    fn empty(&self) -> AnyBox {
        Arc::new(None::<T>)
    }
}

impl<T, E> Monoid for Result<T, E>
where
    T: TypeOps + Clone + 'static,
    E: TypeOps + Clone + 'static
{
    fn empty(&self) -> AnyBox {
        Arc::new(Ok::<T, E>(unsafe { std::mem::zeroed() }))
    }
}

impl Monoid for bool {
    fn empty(&self) -> AnyBox {
        Arc::new(true)
    }
}

impl Monoid for i32 {
    fn empty(&self) -> AnyBox {
        Arc::new(0i32)
    }
}

impl Monoid for i64 {
    fn empty(&self) -> AnyBox {
        Arc::new(0i64)
    }
}

impl Monoid for f32 {
    fn empty(&self) -> AnyBox {
        Arc::new(0.0f32)
    }
}

impl Monoid for f64 {
    fn empty(&self) -> AnyBox {
        Arc::new(0.0f64)
    }
}
