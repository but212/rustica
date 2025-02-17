use crate::prelude::*;

/// Represents a choice between two types, or both.
///
/// # Type Parameters
///
/// * `L`: The left type.
/// * `R`: The right type.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::choice::Choice;
///
/// let left: Choice<i32, String> = Choice::Left(42);
/// let right: Choice<i32, String> = Choice::Right("Hello".to_string());
/// let both: Choice<i32, String> = Choice::Both(42, "Hello".to_string());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Choice<L: TypeConstraints, R: TypeConstraints> {
    /// The left variant.
    Left(L),
    /// The right variant.
    Right(R),
    /// Both left and right variants.
    Both(L, R),
}

impl<L: TypeConstraints, R: TypeConstraints> Default for Choice<L, R> {
    /// Returns a default instance of `Choice`, which is `Left(Default::default())`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let default_choice: Choice<i32, String> = Choice::default();
    /// assert!(default_choice.is_left());
    /// ```
    fn default() -> Self {
        Choice::Left(Default::default())
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Choice<L, R> {
    /// Creates a new `Choice` with a left value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let left = Choice::<i32, String>::make_left(42);
    /// assert!(left.is_left());
    /// ```
    pub fn make_left(value: L) -> Self {
        Choice::Left(value)
    }

    /// Creates a new `Choice` with a right value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let right = Choice::<i32, String>::make_right("Hello".to_string());
    /// assert!(right.is_right());
    /// ```
    pub fn make_right(value: R) -> Self {
        Choice::Right(value)
    }

    /// Creates a new `Choice` with both left and right values.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let both = Choice::<i32, String>::make_both(42, "Hello".to_string());
    /// assert!(both.is_both());
    /// ```
    pub fn make_both(left: L, right: R) -> Self {
        Choice::Both(left, right)
    }

    /// Checks if the `Choice` is a `Left` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let left: Choice<i32, String> = Choice::Left(42);
    /// assert!(left.is_left());
    /// ```
    pub fn is_left(&self) -> bool {
        matches!(self, Choice::Left(_))
    }

    /// Checks if the `Choice` is a `Right` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let right: Choice<i32, String> = Choice::Right("Hello".to_string());
    /// assert!(right.is_right());
    /// ```
    pub fn is_right(&self) -> bool {
        matches!(self, Choice::Right(_))
    }

    /// Checks if the `Choice` is a `Both` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let both: Choice<i32, String> = Choice::Both(42, "Hello".to_string());
    /// assert!(both.is_both());
    /// ```
    pub fn is_both(&self) -> bool {
        matches!(self, Choice::Both(_, _))
    }

    /// Unwraps the left value.
    ///
    /// # Panics
    ///
    /// Panics if the `Choice` is a `Right` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let left: Choice<i32, String> = Choice::Left(42);
    /// assert_eq!(*left.unwrap_left(), 42);
    ///
    /// let both: Choice<i32, String> = Choice::Both(42, "Hello".to_string());
    /// assert_eq!(*both.unwrap_left(), 42);
    /// ```
    pub fn unwrap_left(&self) -> &L {
        match self {
            Choice::Left(l) => l,
            Choice::Right(_) => panic!("Called `unwrap_left` on a `Right` value"),
            Choice::Both(l, _) => l,
        }
    }

    /// Unwraps the right value.
    ///
    /// # Panics
    ///
    /// Panics if the `Choice` is a `Left` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let right: Choice<i32, String> = Choice::Right("Hello".to_string());
    /// assert_eq!(right.unwrap_right(), "Hello");
    ///
    /// let both: Choice<i32, String> = Choice::Both(42, "Hello".to_string());
    /// assert_eq!(both.unwrap_right(), "Hello");
    /// ```
    pub fn unwrap_right(&self) -> &R {
        match self {
            Choice::Left(_) => panic!("Called `unwrap_right` on a `Left` value"),
            Choice::Right(r) => r,
            Choice::Both(_, r) => r,
        }
    }

    /// Unwraps both values.
    ///
    /// # Panics
    ///
    /// Panics if the `Choice` is not a `Both` variant.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let both: Choice<i32, String> = Choice::Both(42, "Hello".to_string());
    /// let (left, right) = both.unwrap_both();
    /// assert_eq!(*left, 42);
    /// assert_eq!(*right, "Hello");
    /// ```
    pub fn unwrap_both(&self) -> (&L, &R) {
        match self {
            Choice::Left(_) => panic!("Called `unwrap_both` on a `Left` value"),
            Choice::Right(_) => panic!("Called `unwrap_both` on a `Right` value"),
            Choice::Both(l, r) => (l, r),
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> HKT for Choice<L, R> {
    type Output<T> = Choice<L, T> where T: TypeConstraints;
}

impl<L: TypeConstraints, R: TypeConstraints> Identity for Choice<L, R> {}

impl<L: TypeConstraints, R: TypeConstraints> Composable for Choice<L, R> {}

impl<L: TypeConstraints, R: TypeConstraints> Category for Choice<L, R> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<L: TypeConstraints, R: TypeConstraints> Arrow for Choice<L, R> {}

impl<L: TypeConstraints, R: TypeConstraints> Functor<R> for Choice<L, R> {
    fn fmap<T: TypeConstraints, F: FnTrait<R, T>>(self, f: F) -> Self::Output<T> {
        match self {
            Choice::Left(l) => Choice::Left(l),
            Choice::Right(r) => Choice::Right(f.call(r)),
            Choice::Both(l, r) => Choice::Both(l, f.call(r)),
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Bifunctor<L, R> for Choice<L, R> {
    type Output<T, U> = Choice<T, U>
    where
        T: TypeConstraints,
        U: TypeConstraints;
    fn bimap<T, U, F, G>(self, f: F, g: G) -> Self::Output<T, U>
    where
        T: TypeConstraints,
        U: TypeConstraints,
        F: FnTrait<L, T>,
        G: FnTrait<R, U>,
    {
        match self {
            Choice::Left(l) => Choice::Left(f.call(l)),
            Choice::Right(r) => Choice::Right(g.call(r)),
            Choice::Both(l, r) => Choice::Both(f.call(l), g.call(r)),
        }
    }

    fn first<T, F>(self, f: F) -> Self::Output<T, R>
    where
        T: TypeConstraints,
        F: FnTrait<L, T>,
    {
        match self {
            Choice::Left(l) => Choice::Left(f.call(l)),
            Choice::Right(r) => Choice::Right(r),
            Choice::Both(l, r) => Choice::Both(f.call(l), r),
        }
    }

    fn second<U, G>(self, g: G) -> Self::Output<L, U>
    where
        U: TypeConstraints,
        G: FnTrait<R, U>,
    {
        match self {
            Choice::Left(l) => Choice::Left(l),
            Choice::Right(r) => Choice::Right(g.call(r)),
            Choice::Both(l, r) => Choice::Both(l, g.call(r)),
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Pure<R> for Choice<L, R> {
    fn pure(value: R) -> Self::Output<R> {
        Choice::Right(value)
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Applicative<R> for Choice<L, R> {
    fn apply<B, F>(self, g: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<R, B>,
    {
        match (self, g) {
            (Choice::Right(x), Choice::Right(f)) => Choice::Right(f.call(x)),
            (Choice::Left(l), _) => Choice::Left(l),
            (Choice::Both(l, _), _) => Choice::Left(l),
            (_, Choice::Left(l)) => Choice::Left(l),
            (_, Choice::Both(l, _)) => Choice::Left(l),
        }
    }

    fn lift2<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(R, B), C>,
    {
        match (self, b) {
            (Choice::Right(x), Choice::Right(y)) => Choice::Right(f.call((x, y))),
            (Choice::Left(l), _) => Choice::Left(l),
            (Choice::Both(l, _), _) => Choice::Left(l),
            (_, Choice::Left(l)) => Choice::Left(l),
            (_, Choice::Both(l, _)) => Choice::Left(l),
        }
    }

    fn lift3<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(R, B, C), D>,
    {
        match (self, b, c) {
            (Choice::Right(x), Choice::Right(y), Choice::Right(z)) => Choice::Right(f.call((x, y, z))),
            (Choice::Left(l), _, _) => Choice::Left(l),
            (Choice::Both(l, _), _, _) => Choice::Left(l),
            (_, Choice::Left(l), _) => Choice::Left(l),
            (_, Choice::Both(l, _), _) => Choice::Left(l),
            (_, _, Choice::Left(l)) => Choice::Left(l),
            (_, _, Choice::Both(l, _)) => Choice::Left(l),
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Monad<R> for Choice<L, R> {
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<R, Self::Output<U>>,
    {
        match self {
            Choice::Right(x) => f.call(x),
            Choice::Left(l) => Choice::Left(l),
            Choice::Both(l, _) => Choice::Left(l),
        }
    }
    
    fn join<U>(self) -> Self::Output<U>
    where
        U: TypeConstraints,
        R: Into<Self::Output<U>>
    {
        match self {
            Choice::Right(x) => x.into(),
            Choice::Left(l) => Choice::Left(l),
            Choice::Both(l, _) => Choice::Left(l),
        }
    }
}