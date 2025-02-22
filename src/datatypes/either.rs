use std::sync::Arc;

use crate::traits::{
    hkt::{TypeOps, AnyBox, HKT},
    pure::Pure,
    functor::Functor,
    applicative::Applicative,
    monad::Monad,
    arrow::Arrow,
    composable::Composable,
    identity::Identity,
    category::Category,
    bifunctor::Bifunctor,
    foldable::Foldable,
    semigroup::Semigroup,
    monoid::Monoid,
    traversable::Traversable,
};

/// A type representing a choice between two types.
///
/// `Either<L, R>` is an enum that can hold either a value of type `L` or a value of type `R`.
/// It is commonly used for error handling, where `L` represents an error type and `R` represents a success type.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::either::Either;
///
/// let success: Either<String, i32> = Either::right(42);
/// let error: Either<String, i32> = Either::left("Error occurred".to_string());
///
/// assert!(success.is_right());
/// assert!(error.is_left());
///
/// let mapped = success.map(|&x| x * 2);
/// assert_eq!(*mapped.unwrap_right(), 84);
/// ```
#[derive(Debug, Clone)]
pub enum Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    /// Represents the left variant of the `Either` type.
    Left(L),
    /// Represents the right variant of the `Either` type.
    Right(R),
}

impl<L, R> Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    /// Creates a new `Either` instance with a left value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in the `Left` variant.
    ///
    /// # Returns
    ///
    /// Returns an `Either<L, R>` containing the left value.
    pub fn left(value: L) -> Self {
        Either::Left(value)
    }

    /// Creates a new `Either` instance with a right value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in the `Right` variant.
    ///
    /// # Returns
    ///
    /// Returns an `Either<L, R>` containing the right value.
    pub fn right(value: R) -> Self {
        Either::Right(value)
    }

    /// Creates a new `Either` instance with a right value.
    ///
    /// This is an alias for `right()`.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in the `Right` variant.
    ///
    /// # Returns
    ///
    /// Returns an `Either<L, R>` containing the right value.
    pub fn new(value: R) -> Self {
        Either::Right(value)
    }

    /// Checks if the `Either` instance is a `Left` variant.
    ///
    /// # Returns
    ///
    /// Returns `true` if the instance is `Left`, `false` otherwise.
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Checks if the `Either` instance is a `Right` variant.
    ///
    /// # Returns
    ///
    /// Returns `true` if the instance is `Right`, `false` otherwise.
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Applies a function to the contained value if the `Either` is `Right`.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `R` and returns a new `R`.
    ///
    /// # Returns
    ///
    /// Returns a new `Either<L, R>` with the function applied to the right value if it exists.
    pub fn map<F>(&self, f: F) -> Either<L, R>
    where
        F: FnOnce(&R) -> R,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    /// Applies a function to the contained value if the `Either` is `Left`.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `L` and returns a new `L`.
    ///
    /// # Returns
    ///
    /// Returns a new `Either<L, R>` with the function applied to the left value if it exists.
    pub fn map_left<F>(&self, f: F) -> Either<L, R>
    where
        F: FnOnce(&L) -> L,
    {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r.clone()),
        }
    }

    /// Maps a function over the `Right` value of an `Either`.
    ///
    /// If the `Either` is `Left`, it returns the `Left` value unchanged.
    /// If it's `Right`, it applies the function to the contained value.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `R` and returns a new `R`.
    ///
    /// # Returns
    ///
    /// A new `Either<L, R>` with the function applied to the right value if it exists.
    pub fn map_right<F>(&self, f: F) -> Either<L, R>
    where
        F: FnOnce(&R) -> R,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    /// Unwraps the `Left` value in the `Either` type.
    ///
    /// # Panics
    ///
    /// Panics if the `Either` is a `Right` value.
    ///
    /// # Returns
    ///
    /// Returns a reference to the contained `Left` value.
    pub fn unwrap_left(&self) -> &L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called unwrap_left on Right value"),
        }
    }

    /// Unwraps the `Right` value in the `Either` type.
    ///
    /// # Panics
    ///
    /// Panics if the `Either` is a `Left` value.
    ///
    /// # Returns
    ///
    /// Returns a reference to the contained `Right` value.
    pub fn unwrap_right(&self) -> &R {
        match self {
            Either::Left(_) => panic!("Called unwrap_right on Left value"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> TypeOps for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone())
    }

    fn equals(&self, other: &AnyBox) -> bool {
        other.downcast_ref::<Self>().map_or(false, |other| match (self, other) {
            (Either::Left(l1), Either::Left(l2)) => l1.equals(&l2.clone_box()),
            (Either::Right(r1), Either::Right(r2)) => r1.equals(&r2.clone_box()),
            _ => false,
        })
    }
}

impl<L, R> HKT for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn apply_type(&self) -> AnyBox {
        self.clone_box()
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Self>().map(|x| x.clone_box())
    }
}

impl<L, R> Pure for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn pure(value: AnyBox) -> AnyBox {
        match value.downcast_ref::<R>() {
            Some(v) => Arc::new(Either::<L, R>::Right(v.clone())),
            None => Arc::new(Either::<L, R>::Right(R::default())),
        }
    }
}

impl<L, R> Identity for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn identity() -> AnyBox {
        Arc::new(Either::<L, R>::Right(R::default()))
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Self::identity())
    }
}

impl<L, R> Functor for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let result = f(Arc::new(r.clone()));
                match result.downcast_ref::<R>() {
                    Some(v) => Arc::new(Either::<L, R>::Right(v.clone())),
                    None => Arc::new(Either::<L, R>::Right(R::default())),
                }
            }
        }
    }
}

impl<L, R> Applicative for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(x) => Arc::new(Either::<L, R>::Left(x.clone())) as AnyBox,
            Either::Right(x) => f(x.clone_box()),
        }
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Either<L, R>>()) {
            (Either::Right(x), Some(Either::Right(y))) => {
                let result = f(x.clone_box(), y.clone_box());
                match result.downcast_ref::<R>() {
                    Some(v) => Arc::new(Either::<L, R>::Right(v.clone())),
                    None => Arc::new(Either::<L, R>::Right(R::default())),
                }
            }
            (Either::Left(l), _) => Arc::new(Either::<L, R>::Left(l.clone())),
            (_, Some(Either::Left(l))) => Arc::new(Either::<L, R>::Left(l.clone())),
            _ => Arc::new(Either::<L, R>::Left(L::default())),
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match (self, b.downcast_ref::<Either<L, R>>(), c.downcast_ref::<Either<L, R>>()) {
            (Either::Right(x), Some(Either::Right(y)), Some(Either::Right(z))) => {
                let result = f(x.clone_box(), y.clone_box(), z.clone_box());
                match result.downcast_ref::<R>() {
                    Some(v) => Arc::new(Either::<L, R>::Right(v.clone())),
                    None => Arc::new(Either::<L, R>::Right(R::default())),
                }
            }
            (Either::Left(l), _, _) => Arc::new(Either::<L, R>::Left(l.clone())),
            (_, Some(Either::Left(l)), _) => Arc::new(Either::<L, R>::Left(l.clone())),
            (_, _, Some(Either::Left(l))) => Arc::new(Either::<L, R>::Left(l.clone())),
            _ => Arc::new(Either::<L, R>::Left(L::default())),
        }
    }
}

impl<L, R> Monad for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let result = f(r.clone_box());
                match result.downcast_ref::<Either<L, R>>() {
                    Some(either) => Arc::new(either.clone()),
                    None => Arc::new(Either::<L, R>::Right(R::default())),
                }
            }
        }
    }

    fn join(&self) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => match r.clone_box().downcast_ref::<Either<L, R>>() {
                Some(inner) => Arc::new(inner.clone()),
                None => Arc::new(Either::<L, R>::Right(R::default())),
            }
        }
    }
}

impl<L, R> Category for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        match (self, other.downcast_ref::<Either<L, R>>()) {
            (Either::Right(_), Some(Either::Right(r2))) => {
                Arc::new(Either::<L, R>::Right(r2.clone()))
            }
            (Either::Left(l), _) => Arc::new(Either::<L, R>::Left(l.clone())),
            (_, Some(Either::Left(l))) => Arc::new(Either::<L, R>::Left(l.clone())),
            _ => Arc::new(Either::<L, R>::Left(L::default())),
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Either::<L, R>::Right(R::default())) as AnyBox
    }
}

impl<L, R> Arrow for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = Arc::clone(func);
            Arc::new(Box::new(move |x: AnyBox| -> AnyBox {
                if let Some(x) = x.downcast_ref::<Either<L, R>>() {
                    match x {
                        Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
                        Either::Right(r) => func(r.clone_box())
                    }
                } else {
                    Arc::new(Either::<L, R>::Left(L::default()))
                }
            }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) as AnyBox
        } else {
            Arc::new(Either::<L, R>::Left(L::default()))
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = Arc::clone(func);
            Arc::new(Box::new(move |pair: AnyBox| -> AnyBox {
                if let Some((a, b)) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                    Arc::new((func(a.clone()), b.clone()))
                } else {
                    pair
                }
            }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) as AnyBox
        } else {
            Arc::new(Either::<L, R>::Left(L::default()))
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let func = Arc::clone(func);
            Arc::new(Box::new(move |pair: AnyBox| -> AnyBox {
                if let Some((a, b)) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                    Arc::new((a.clone(), func(b.clone())))
                } else {
                    pair
                }
            }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) as AnyBox
        } else {
            Arc::new(Either::<L, R>::Left(L::default()))
        }
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        if let (Some(f), Some(g)) = (
            f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
            g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
        ) {
            let f = Arc::clone(f);
            let g = Arc::clone(g);
            Arc::new(Box::new(move |pair: AnyBox| -> AnyBox {
                if let Some((a, b)) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                    Arc::new((f(a.clone()), g(b.clone())))
                } else {
                    pair
                }
            }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) as AnyBox
        } else {
            Arc::new(Either::<L, R>::Left(L::default()))
        }
    }
}

impl<L, R> Composable for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn compose(&self, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x: AnyBox| -> AnyBox {
            let gx = g(x);
            f(gx)
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let result = f(Arc::new(r.clone()));
                match result.downcast_ref::<R>() {
                    Some(v) => Arc::new(Either::<L, R>::Right(v.clone())),
                    None => Arc::new(Either::<L, R>::Right(R::default())),
                }
            }
        }
    }
}

impl<L: TypeOps + Clone + Default + Send + Sync + 'static, R: TypeOps + Clone + Default + Send + Sync + 'static> Bifunctor for Either<L, R> {
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let result = f(r.clone_box());
                if let Some(value) = result.downcast_ref::<Either<L, R>>() {
                    value.clone_box()
                } else {
                    Arc::new(Either::<L, R>::Left(L::default()))
                }
            }
        }
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let result = f(r.clone_box());
                if let Some(value) = result.downcast_ref::<Either<L, R>>() {
                    value.clone_box()
                } else {
                    Arc::new(Either::<L, R>::Left(L::default()))
                }
            }
        }
    }

    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(l) => {
                let result = f(l.clone_box());
                if let Some(value) = result.downcast_ref::<Either<L, R>>() {
                    value.clone_box()
                } else {
                    Arc::new(Either::<L, R>::Left(L::default()))
                }
            },
            Either::Right(r) => {
                let result = g(r.clone_box());
                if let Some(value) = result.downcast_ref::<Either<L, R>>() {
                    value.clone_box()
                } else {
                    Arc::new(Either::<L, R>::Left(L::default()))
                }
            }
        }
    }
}

impl<L, R> Foldable for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(_) => init,
            Either::Right(r) => f(init, r.clone_box())
        }
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(_) => init,
            Either::Right(r) => f(r.clone_box(), init)
        }
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Either::Left(_) => Arc::new(()),
            Either::Right(r) => f(r.clone_box())
        }
    }
}

impl<L, R> Traversable for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static,
    {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                let fr = f(r.clone_box());
                match fr.downcast_ref::<Either<L, R>>() {
                    Some(either) => either.clone_box(),
                    None => Arc::new(Either::<L, R>::Left(L::default()))
                }
            }
        }
    }

    fn distribute(&self) -> AnyBox {
        match self {
            Either::Left(l) => Arc::new(Either::<L, R>::Left(l.clone())),
            Either::Right(r) => {
                match r.clone_box().downcast_ref::<Either<L, R>>() {
                    Some(either) => either.clone_box(),
                    None => Arc::new(Either::<L, R>::Left(L::default()))
                }
            }
        }
    }
}

impl<L, R> Semigroup for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn combine(&self, other: AnyBox) -> AnyBox {
        if let Some(other) = other.downcast_ref::<Either<L, R>>() {
            match (self, other) {
                (Either::Right(_), Either::Right(b)) => Arc::new(Either::<L, R>::Right(b.clone())),
                (Either::Right(r), _) => Arc::new(Either::<L, R>::Right(r.clone())),
                (_, Either::Right(b)) => Arc::new(Either::<L, R>::Right(b.clone())),
                _ => Arc::new(Either::<L, R>::Left(L::default()))
            }
        } else {
            Arc::new(Either::<L, R>::Left(L::default()))
        }
    }
}

impl<L, R> Monoid for Either<L, R>
where
    L: TypeOps + Clone + Default + Send + Sync + 'static,
    R: TypeOps + Clone + Default + Send + Sync + 'static,
{
    fn empty(&self) -> AnyBox {
        Arc::new(Either::<L, R>::Left(L::default()))
    }
}