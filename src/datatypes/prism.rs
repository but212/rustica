#![doc = include_str!("../../docs/datatypes/prism.md")]

use core::marker::PhantomData;

/// A `Prism` is an optic that allows focusing on a specific case of a sum type.
///
/// It provides a way to:
/// - Borrow a reference to a variant's payload (`preview(&self, &S) -> Option<&A>`) with 0 heap allocations
/// - Construct a sum type value from a focus value (`review(&self, A) -> S`)
/// - Update variants with zero-allocation short-circuiting on unchanged values (`set`, `modify`)
///
/// # Type Parameters
///
/// * `S` - The source sum type (typically an enum)
/// * `A` - The focus type (the variant's inner payload)
/// * `PreviewFn` - The closure type for inspecting a variant: `Fn(&S) -> Option<&A>`
/// * `ReviewFn` - The closure type for constructing a sum type: `Fn(A) -> S`
///
/// # Type Class Laws
///
/// A well-behaved Prism satisfies:
/// 1. **Review-Preview**: `prism.preview(&prism.review(a)) == Some(&a)`
/// 2. **Preview-Review**: `prism.preview(&s) == Some(&a) => prism.review(a.clone()) == s` (for lawful sum types)
/// 3. **Unchanged Short-Circuit**: `prism.preview(&s) == Some(&new_value) => prism.set(s, new_value) == s` (0 B allocation; equality is `PartialEq`. For bit-exact types such as `f64` where `-0.0 == 0.0` or non-reflexive types such as `NaN`, prefer `set_always`, which never short-circuits)
pub struct Prism<S, A, PreviewFn, ReviewFn> {
    /// Function that attempts to borrow a reference to type A from S
    preview: PreviewFn,
    /// Function that constructs a value of type S from A
    review: ReviewFn,
    _phantom: PhantomData<fn(S) -> A>,
}

impl<S, A, PreviewFn, ReviewFn> Clone for Prism<S, A, PreviewFn, ReviewFn>
where
    PreviewFn: Clone,
    ReviewFn: Clone,
{
    fn clone(&self) -> Self {
        Self {
            preview: self.preview.clone(),
            review: self.review.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<S, A, PreviewFn, ReviewFn> core::fmt::Debug for Prism<S, A, PreviewFn, ReviewFn> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Prism").finish_non_exhaustive()
    }
}

impl<S, A, PreviewFn, ReviewFn> Prism<S, A, PreviewFn, ReviewFn>
where
    PreviewFn: Fn(&S) -> Option<&A>,
    ReviewFn: Fn(A) -> S,
{
    /// Creates a new reference-borrowing Prism.
    ///
    /// The `preview` closure extracts a reference to the variant's payload if present,
    /// without cloning the focus.
    ///
    /// # Arguments
    ///
    /// * `preview` - Closure returning `Option<&A>` from `&S`
    /// * `review` - Closure constructing `S` from `A`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Result<T, E> { Ok(T), Err(E) }
    ///
    /// let ok_prism = Prism::new(
    ///     |r: &Result<i32, String>| match r {
    ///         Result::Ok(v) => Some(v),
    ///         Result::Err(_) => None,
    ///     },
    ///     Result::Ok,
    /// );
    /// ```
    pub const fn new(preview: PreviewFn, review: ReviewFn) -> Self {
        Prism {
            preview,
            review,
            _phantom: PhantomData,
        }
    }

    /// Extracts a borrowed reference to the focused value, if present, with zero heap allocations.
    #[inline]
    pub fn preview<'s>(&self, source: &'s S) -> Option<&'s A> {
        (self.preview)(source)
    }

    /// Extracts an owned clone of the focused value, adhering to `C-CONV` conventions.
    #[inline]
    pub fn to_value(&self, source: &S) -> Option<A>
    where
        A: Clone,
    {
        (self.preview)(source).cloned()
    }

    /// Constructs a value of type `S` from `A`.
    #[inline]
    pub fn review(&self, a: A) -> S {
        (self.review)(a)
    }

    /// Sets the focused value with zero-allocation short-circuiting.
    ///
    /// Assumes a lawful prism (`preview(s) == Some(a) => review(a) == s`).
    /// - If `new_value == current` under `PartialEq`, returns `source` untouched (0 B, 0 clones).
    /// - If variant does not match (`None`), returns `source` untouched.
    /// - If values differ, reconstructs `S` via `review(new_value)`.
    ///
    /// Note: Equality check uses `PartialEq`. For bit-exact preservation (such as distinguishing `-0.0` and `0.0`
    /// on `f64`) or non-reflexive types (`NaN`), use [`Prism::set_always`].
    /// To preserve non-focus fields of `source` on mutation, use [`Prism::set_with`].
    #[inline]
    pub fn set(&self, source: S, new_value: A) -> S
    where
        A: PartialEq,
    {
        match (self.preview)(&source) {
            Some(cur) if cur == &new_value => source,
            Some(_) => (self.review)(new_value),
            None => source,
        }
    }

    /// Unconditionally reconstructs the focused variant when matched.
    #[inline]
    pub fn set_always(&self, source: S, new_value: A) -> S {
        match (self.preview)(&source) {
            Some(_) => (self.review)(new_value),
            None => source,
        }
    }

    /// Modifies the focused value with single-clone and zero-allocation short-circuiting.
    ///
    /// Clones `current` exactly 1 time to pass owned value to `f(current)`.
    /// If `f` returns an identical value (`cur == &new_val`) under `PartialEq`, returns `source` untouched (0 B).
    /// If values differ, reconstructs `S` via `review(new_val)`.
    ///
    /// Note: Equality check uses `PartialEq`. For bit-exact types or non-reflexive types,
    /// use [`Prism::modify_always`].
    /// To preserve non-focus fields of `source` on mutation, use [`Prism::modify_with`].
    #[inline]
    pub fn modify<F>(&self, source: S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        A: Clone + PartialEq,
    {
        match (self.preview)(&source) {
            Some(cur) => {
                let new_val = f(cur.clone());
                if cur == &new_val {
                    source
                } else {
                    (self.review)(new_val)
                }
            },
            None => source,
        }
    }

    /// Modifies the focused value unconditionally when matched.
    #[inline]
    pub fn modify_always<F>(&self, source: S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        A: Clone,
    {
        match (self.preview)(&source) {
            Some(cur) => (self.review)(f(cur.clone())),
            None => source,
        }
    }

    /// Modifies the focused value while preserving non-focus data from `source`.
    #[inline]
    pub fn modify_with<M, F>(&self, source: S, modify_fn: M, f: F) -> S
    where
        M: FnOnce(S, A) -> S,
        F: FnOnce(A) -> A,
        A: Clone,
    {
        match (self.preview)(&source) {
            Some(current_value) => {
                let val = current_value.clone();
                modify_fn(source, f(val))
            },
            None => source,
        }
    }

    /// Sets the focused value to a new value while preserving non-focus data from `source`.
    #[inline]
    pub fn set_with<M>(&self, source: S, modify_fn: M, new_value: A) -> S
    where
        M: FnOnce(S, A) -> S,
    {
        if (self.preview)(&source).is_some() {
            modify_fn(source, new_value)
        } else {
            source
        }
    }
}

#[inline]
fn compose_prism_views<S, A: 'static, B, V1, V2>(
    v1: V1, v2: V2,
) -> impl Fn(&S) -> Option<&B> + Clone
where
    V1: Fn(&S) -> Option<&A> + Clone,
    V2: Fn(&A) -> Option<&B> + Clone,
{
    move |s: &S| v1(s).and_then(&v2)
}

impl<S, A, PreviewFn, ReviewFn> Prism<S, A, PreviewFn, ReviewFn>
where
    ReviewFn: Fn(A) -> S + Clone,
    PreviewFn: Fn(&S) -> Option<&A> + Clone,
{
    /// Composes two prisms, preserving zero-allocation reference borrowing.
    ///
    /// Given a prism from `S` to `A` and a prism from `A` to `B`, creates a new
    /// prism from `S` directly to `B`.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn then<B, PreviewFn2, ReviewFn2>(
        self, other: Prism<A, B, PreviewFn2, ReviewFn2>,
    ) -> Prism<S, B, impl Fn(&S) -> Option<&B> + Clone, impl Fn(B) -> S + Clone>
    where
        A: 'static,
        ReviewFn2: Fn(B) -> A + Clone,
        PreviewFn2: Fn(&A) -> Option<&B> + Clone,
    {
        let preview_composed = compose_prism_views(self.preview, other.preview);
        let review1 = self.review;
        let review2 = other.review;

        Prism {
            preview: preview_composed,
            review: move |b: B| review1(review2(b)),
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use alloc::{boxed::Box, collections::BTreeMap, format, string::String};

    use super::Prism;

    #[derive(Clone, Debug, PartialEq)]
    struct ErrorInfo {
        code: u32,
        message: String,
    }

    #[derive(Clone, Debug, PartialEq)]
    enum Status {
        Active(String),
        Inactive,
        Error(ErrorInfo),
    }

    type ActivePrism = Prism<
        Status,
        String,
        Box<dyn Fn(&Status) -> Option<&String>>,
        Box<dyn Fn(String) -> Status>,
    >;

    fn active_prism() -> ActivePrism {
        Prism::new(
            Box::new(|s| match s {
                Status::Active(name) => Some(name),
                _ => None,
            }),
            Box::new(Status::Active),
        )
    }

    #[test]
    fn preview_review_and_modify_obey_prism_contracts() {
        let prism = active_prism();
        let target = Status::Active("Alice".into());
        assert_eq!(prism.preview(&target), Some(&"Alice".into()));
        assert_eq!(prism.to_value(&target), Some("Alice".into()));
        assert_eq!(prism.preview(&Status::Inactive), None);
        assert_eq!(prism.review("Bob".into()), Status::Active("Bob".into()));
        assert_eq!(
            prism.preview(&prism.review("LawCheck".into())),
            Some(&"LawCheck".into())
        );

        let error_prism = Prism::new(
            |s: &Status| match s {
                Status::Error(info) => Some(info),
                _ => None,
            },
            Status::Error,
        );

        let error = Status::Error(ErrorInfo {
            code: 500,
            message: "Fail".into(),
        });

        assert_eq!(
            error_prism.modify(error.clone(), |info| ErrorInfo {
                code: info.code + 1,
                message: format!("{}-fixed", info.message),
            }),
            Status::Error(ErrorInfo {
                code: 501,
                message: "Fail-fixed".into()
            })
        );
        assert_eq!(
            active_prism().modify(Status::Inactive, |_| "ignored".into()),
            Status::Inactive
        );
        assert_eq!(
            error_prism.set(
                error,
                ErrorInfo {
                    code: 200,
                    message: "OK".into()
                }
            ),
            Status::Error(ErrorInfo {
                code: 200,
                message: "OK".into()
            })
        );
    }

    #[test]
    fn complex_extraction_and_composition_work() {
        #[derive(Debug, Clone, PartialEq)]
        enum ConfigValue {
            Integer(i64),
            String(String),
            Dictionary(BTreeMap<String, ConfigValue>),
        }

        let dict = Prism::new(
            |value: &ConfigValue| match value {
                ConfigValue::Dictionary(map) => Some(map),
                _ => None,
            },
            ConfigValue::Dictionary,
        );

        let mut values = BTreeMap::new();
        values.insert("name".into(), ConfigValue::String("Alice".into()));
        values.insert("age".into(), ConfigValue::Integer(30));
        let mut updated_values = values.clone();
        updated_values.insert("theme".into(), ConfigValue::String("dark".into()));
        let updated = dict.review(updated_values);
        let new_values = dict.preview(&updated).unwrap();
        assert_eq!(new_values.len(), 3);
        assert!(new_values.contains_key("theme"));

        #[derive(Debug, Clone, PartialEq)]
        enum Inner {
            Val(i32),
            Empty,
        }

        #[derive(Debug, Clone, PartialEq)]
        enum Outer {
            Nested(Inner),
            Other,
        }

        let outer = Prism::new(
            |value: &Outer| match value {
                Outer::Nested(inner) => Some(inner),
                _ => None,
            },
            Outer::Nested,
        );

        let inner = Prism::new(
            |value: &Inner| match value {
                Inner::Val(value) => Some(value),
                Inner::Empty => None,
            },
            Inner::Val,
        );

        let deep = outer.then(inner);
        assert_eq!(deep.preview(&Outer::Nested(Inner::Val(42))), Some(&42));
        assert_eq!(deep.review(100), Outer::Nested(Inner::Val(100)));
        assert_eq!(deep.preview(&Outer::Nested(Inner::Empty)), None);
        assert_eq!(deep.preview(&Outer::Other), None);
    }

    #[test]
    fn set_preserves_source_when_focus_is_absent() {
        let inactive = Status::Inactive;
        let result = active_prism().set(inactive, "Charlie".into());
        assert_eq!(result, Status::Inactive);
    }

    type ConstStatusPrism =
        Prism<Status, String, fn(&Status) -> Option<&String>, fn(String) -> Status>;

    #[test]
    fn prism_is_const_constructible() {
        const fn make_prism() -> ConstStatusPrism {
            Prism::new(
                |s: &Status| match s {
                    Status::Active(name) => Some(name),
                    _ => None,
                },
                Status::Active,
            )
        }
        const CONST_PRISM: ConstStatusPrism = make_prism();
        let target = Status::Active("Const".into());
        assert_eq!(CONST_PRISM.preview(&target), Some(&"Const".into()));
    }
}
