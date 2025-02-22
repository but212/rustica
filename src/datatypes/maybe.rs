use std::sync::Arc;
use crate::prelude::*;

/// A type that represents an optional value.
///
/// `Maybe` is a container for an optional value. It can either contain a value (`Just`),
/// or be empty (`Nothing`). This is similar to Rust's built-in `Option` type, but with
/// additional functionality and compatibility with the `rustica` library's type system.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::maybe::Maybe;
///
/// // Creating Maybe instances
/// let just_int = Maybe::just(42);
/// let just_string = Maybe::just("Hello, Rustica!");
/// let nothing = Maybe::nothing();
///
/// // Checking the state of Maybe instances
/// assert!(just_int.is_just());
/// assert!(just_string.is_just());
/// assert!(nothing.is_nothing());
///
/// // Unwrapping and getting values
/// assert_eq!(just_int.unwrap().downcast_ref::<i32>(), Some(&42));
/// assert_eq!(just_string.unwrap().downcast_ref::<&str>(), Some(&"Hello, Rustica!"));
///
/// // Using get() with different types
/// assert_eq!(just_int.get::<i32>(), Some(42));
/// assert_eq!(just_int.get::<String>(), None);  // Mismatched type
///
/// // Demonstrating safety of unwrap() and get()
/// // Uncommenting the following line would panic:
/// // let _ = nothing.unwrap();
///
/// assert_eq!(nothing.get::<i32>(), None);
/// ```
#[derive(Clone)]
pub struct Maybe {
    /// The inner value of the Maybe type, wrapped in an Option.
    inner: Option<AnyBox>,
}

impl Maybe {
    /// Creates a new `Maybe` instance with a `Just` value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in the `Maybe` instance.
    ///
    /// # Returns
    ///
    /// A new `Maybe` instance containing the provided value.
    pub fn just<T: TypeOps + Send + Sync + 'static>(value: T) -> Self {
        Maybe {
            inner: Some(Arc::new(value) as AnyBox),
        }
    }

    /// Creates a new `Maybe` instance representing `Nothing`.
    ///
    /// # Returns
    ///
    /// A new `Maybe` instance with no value (Nothing).
    pub fn nothing() -> Self {
        Maybe { inner: None }
    }

    /// Checks if the `Maybe` instance contains a value (Just).
    ///
    /// # Returns
    ///
    /// `true` if the instance contains a value, `false` otherwise.
    pub fn is_just(&self) -> bool {
        self.inner.is_some()
    }

    /// Checks if the `Maybe` instance is empty (Nothing).
    ///
    /// # Returns
    ///
    /// `true` if the instance is empty, `false` otherwise.
    pub fn is_nothing(&self) -> bool {
        self.inner.is_none()
    }

    /// Unwraps the value contained in the `Maybe` instance.
    ///
    /// # Panics
    ///
    /// Panics if the `Maybe` instance is `Nothing`.
    ///
    /// # Returns
    ///
    /// The contained value as an `AnyBox`.
    pub fn unwrap(&self) -> AnyBox {
        self.inner.clone().expect("Tried to unwrap a Nothing value!")
    }

    /// Attempts to get the value of a specific type from the `Maybe` instance.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The expected type of the contained value.
    ///
    /// # Returns
    ///
    /// `Some(T)` if the instance contains a value of type `T`, `None` otherwise.
    pub fn get<T: TypeOps + Send + Sync + Clone + 'static>(&self) -> Option<T> {
        self.inner.as_ref().and_then(|x| x.downcast_ref::<T>().cloned())
    }
}

impl Default for Maybe {
    fn default() -> Self {
        Maybe::nothing()
    }
}

impl HKT for Maybe {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        if let Some(maybe) = boxed.downcast_ref::<Maybe>() {
            Some(Arc::new(maybe.clone()) as AnyBox)
        } else {
            None
        }
    }
}

impl Pure for Maybe {
    fn pure(value: AnyBox) -> AnyBox {
        value
    }
}

impl Identity for Maybe {
    fn identity() -> AnyBox {
        Arc::new(Maybe::nothing()) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync + 'static>) -> AnyBox {
        f(Self::identity())
    }
}

impl Functor for Maybe {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => Arc::new(Maybe::just_box(f(value.clone()))) as AnyBox,
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Applicative for Maybe {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Maybe { inner: Some(x) } => f(x.clone()),
            Maybe { inner: None } => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (&self.inner, b.downcast_ref::<Maybe>()) {
            (Some(a_val), Some(b_maybe)) => {
                if let Some(b_val) = b_maybe.inner.as_ref() {
                    Arc::new(Maybe::just_box(f(a_val.clone(), b_val.clone()))) as AnyBox
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            _ => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (&self.inner, b.downcast_ref::<Maybe>(), c.downcast_ref::<Maybe>()) {
            (Some(a_val), Some(b_maybe), Some(c_maybe)) => {
                if let (Some(b_val), Some(c_val)) = (b_maybe.inner.as_ref(), c_maybe.inner.as_ref()) {
                    Arc::new(Maybe::just_box(f(a_val.clone(), b_val.clone(), c_val.clone()))) as AnyBox
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            _ => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Arrow for Maybe {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let Some(f) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                    f(value.clone())
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let Some(f) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                    f(value.clone())
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let Some(f) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
                    f(value.clone())
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let (Some(f), Some(g)) = (
                    f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
                    g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
                ) {
                    let result_f = f(value.clone());
                    let result_g = g(value.clone());
                    let tuple = (result_f, result_g);
                    Arc::new(tuple) as AnyBox
                } else {
                    Arc::new(Maybe::nothing()) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Composable for Maybe {
    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x: AnyBox| {
            let g_result = g(x);
            f(g_result)
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => f(value.clone()),
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Bifunctor for Maybe {
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => {
                let result_f = f(value.clone());
                g(result_f)
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(f, Arc::new(|x| x))
    }

    fn map_second(&self, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(Arc::new(|x| x), g)
    }
}

impl Monad for Maybe {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => {
                let result = f(value.clone());
                if let Some(maybe) = result.downcast_ref::<Maybe>() {
                    Arc::new(maybe.clone()) as AnyBox
                } else {
                    Arc::new(Maybe::just_box(result)) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn join(&self) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let Some(inner_maybe) = value.downcast_ref::<Maybe>() {
                    Arc::new(inner_maybe.clone()) as AnyBox
                } else {
                    Arc::new(Maybe::just_box(value.clone())) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Semigroup for Maybe {
    fn combine(&self, other: AnyBox) -> AnyBox {
        match (&self.inner, other.downcast_ref::<Maybe>()) {
            (Some(a), Some(other_maybe)) => {
                if let Some(b) = other_maybe.inner.as_ref() {
                    Arc::new(Maybe::just_box(b.clone())) as AnyBox
                } else {
                    Arc::new(Maybe::just_box(a.clone())) as AnyBox
                }
            }
            (None, Some(other_maybe)) => Arc::new(other_maybe.clone()) as AnyBox,
            _ => Arc::new(self.clone()) as AnyBox,
        }
    }
}

impl Monoid for Maybe {
    fn empty(&self) -> AnyBox {
        Arc::new(Maybe::nothing()) as AnyBox
    }
}

impl Foldable for Maybe {
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => f(init, value.clone()),
            None => init,
        }
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => f(value.clone(), init),
            None => init,
        }
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match &self.inner {
            Some(value) => f(value.clone()),
            None => self.empty(),
        }
    }
}

impl Traversable for Maybe {
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static
    {
        match &self.inner {
            Some(value) => {
                let result = f(value.clone());
                if let Some(maybe) = result.downcast_ref::<Maybe>() {
                    Arc::new(maybe.clone()) as AnyBox
                } else {
                    Arc::new(Maybe::just_box(result)) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }

    fn distribute(&self) -> AnyBox {
        match &self.inner {
            Some(value) => {
                if let Some(inner_maybe) = value.downcast_ref::<Maybe>() {
                    Arc::new(inner_maybe.clone()) as AnyBox
                } else {
                    Arc::new(Maybe::just_box(value.clone())) as AnyBox
                }
            }
            None => Arc::new(Maybe::nothing()) as AnyBox,
        }
    }
}

impl Maybe {
    /// Helper function to create a Maybe from an AnyBox
    fn just_box(value: AnyBox) -> Self {
        Maybe {
            inner: Some(value),
        }
    }
}
