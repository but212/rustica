use crate::prelude::*;
use crate::datatypes::choice::Choice;

/// A Prism is an optic that focuses on a particular case of a sum type.
/// 
/// # Type Parameters
/// * `S` - The source type (the sum type)
/// * `A` - The focus type (the case we're interested in)
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Prism<S: TypeConstraints, A: TypeConstraints> {
    /// Attempts to extract a value of type A from S
    preview: FnType<S, Option<A>>,
    /// Constructs a value of type S from A
    review: FnType<A, S>,
}

impl<S, A> Prism<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    /// Creates a new Prism.
    ///
    /// # Arguments
    /// * `preview` - A function that attempts to extract a value of type A from S
    /// * `review` - A function that constructs a value of type S from A
    ///
    /// # Returns
    /// A new `Prism<S, A>`
    pub fn new<P, R>(preview: P, review: R) -> Self
    where
        P: Fn(S) -> Option<A> + Clone + Send + Sync + 'static,
        R: Fn(A) -> S + Clone + Send + Sync + 'static,
    {
        Prism {
            preview: FnType::new(preview),
            review: FnType::new(review),
        }
    }

    /// Attempts to extract a value of type A from S.
    ///
    /// # Arguments
    /// * `s` - A value of type S
    ///
    /// # Returns
    /// An `Option<A>` containing the extracted value if successful, or `None` if not
    pub fn preview(&self, s: S) -> Option<A> {
        self.preview.call(s)
    }

    /// Constructs a value of type S from A.
    ///
    /// # Arguments
    /// * `a` - A value of type A
    ///
    /// # Returns
    /// A value of type S
    pub fn review(&self, a: A) -> S {
        self.review.call(a)
    }

    /// Creates a Prism for a specific case of an enum.
    ///
    /// # Arguments
    /// * `match_case` - A function that matches and extracts a specific case from the enum
    /// * `make_case` - A function that constructs the enum for a specific case
    ///
    /// # Returns
    /// A new `Prism<S, A>` for the specified case
    pub fn for_case<F, G>(match_case: F, make_case: G) -> Self
    where
        F: Fn(S) -> Option<A> + Clone + Send + Sync + 'static,
        G: Fn(A) -> S + Clone + Send + Sync + 'static,
    {
        Prism::new(match_case, make_case)
    }
}

// Example usage with Choice type
impl<L: TypeConstraints, R: TypeConstraints> Choice<L, R> {
    /// Creates a Prism focusing on the Left case.
    pub fn left_prism() -> Prism<Self, L> {
        Prism::for_case(
            |choice| match choice {
                Choice::Left(l) => Some(l),
                _ => None,
            },
            Choice::Left,
        )
    }

    /// Creates a Prism focusing on the Right case.
    pub fn right_prism() -> Prism<Self, R> {
        Prism::for_case(
            |choice| match choice {
                Choice::Right(r) => Some(r),
                _ => None,
            },
            Choice::Right,
        )
    }

    /// Creates a Prism focusing on the Both case.
    pub fn both_prism() -> Prism<Self, (L, R)> {
        Prism::for_case(
            |choice| match choice {
                Choice::Both(l, r) => Some((l, r)),
                _ => None,
            },
            |(l, r)| Choice::Both(l, r),
        )
    }
}

impl<S: TypeConstraints, A: TypeConstraints> HKT for Prism<S, A> {
    type Output<T> = Prism<S, T> where T: TypeConstraints;
}