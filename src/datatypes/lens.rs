use crate::prelude::*;

/// A lens that focuses on a field of a struct.
/// 
/// # Type Parameters
/// * `S` - The type of the larger structure
/// * `A` - The type of the focused part
/// 
/// # Laws
/// A Lens instance must satisfy these laws:
/// 1. Get-Put Identity: For any structure `s`,
///    `s.put(s.get()) = s`
/// 2. Put-Get Identity: For any structure `s` and value `a`,
///    `(s.put(a)).get() = a`
/// 3. Put-Put Identity: For any structure `s` and values `a`, `b`,
///    `s.put(a).put(b) = s.put(b)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(s.get()) = η(s).get()`
/// 5. Composition: For any lenses `l1`, `l2`,
///    `(l1.compose(l2)).get() = l2.get(l1.get())`
/// 6. Focus Preservation: For any structure `s` and function `f`,
///    `s.modify(f) = s.put(f(s.get()))`
/// 7. Type Safety: For any structure `s` and value `a`,
///    `s.put(a)` must maintain type safety of the structure
/// 8. Immutability: For any structure `s`,
///    Original structure must remain unchanged after lens operations
///
/// # Examples
///
/// ```
/// use rustica::datatypes::lens::Lens;
///
/// #[derive(Default, Eq, PartialEq, Debug, Clone)]
/// struct MyStruct {
///     field: i32,
/// }
///
/// let lens = Lens::new(|s: MyStruct| s.field, |s, f| MyStruct { field: f });
/// let my_struct = MyStruct { field: 42 };
/// let modified_struct = lens.set(my_struct, 100);
/// assert_eq!(lens.get(&modified_struct), 100);
/// ```
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub struct Lens<S: TypeConstraints, A: TypeConstraints> {
    // Fields to store the `get` and `set` functions.
    get: FnType<S, A>,
    set: FnType<(S, A), S>,
}

impl<S: TypeConstraints, A: TypeConstraints> Lens<S, A> {
    /// Creates a new lens.
    ///
    /// # Arguments
    ///
    /// * `get` - A function to get the value of the field.
    /// * `set` - A function to set the value of the field.
    pub fn new<G, H>(get: G, set: H) -> Self
    where
        G: Fn(S) -> A + Clone + Send + Sync + 'static,
        H: Fn(S, A) -> S + Clone + Send + Sync + 'static,
    {
        Lens {
            get: FnType::new(move |s| get(s)),
            set: FnType::new(move |(s, a)| set(s, a)),
        }
    }

    /// Gets the field value from the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct from which to get the value.
    ///
    /// # Returns
    ///
    /// The value of the field.
    pub fn get(&self, s: &S) -> A {
        self.get.call(s.clone())
    }

    /// Sets the field value in the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct in which to set the value.
    /// * `a` - The value to set.
    ///
    /// # Returns
    ///
    /// The updated struct.
    pub fn set(&self, s: S, a: A) -> S {
        self.set.call((s, a))
    }

    /// Modifies the field value in the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct in which to modify the value.
    /// * `f` - A function to modify the value.
    ///
    /// # Returns
    ///
    /// The updated struct.
    pub fn modify<F>(&self, s: S, f: F) -> S
    where
        F: Fn(A) -> A + Clone + Send + Sync + 'static,
    {
        let a = self.get.call(s.clone());
        let f = FnType::new(f);
        self.set.call((s, f.call(a)))
    }

    /// Composes this lens with another lens.
    ///
    /// # Arguments
    ///
    /// * `other` - The other lens to compose with.
    ///
    /// # Returns
    ///
    /// A new lens that is the composition of this lens and the other lens.
    pub fn compose_lens<B>(self, other: Lens<A, B>) -> Lens<S, B>
    where
        B: TypeConstraints,
    {
        let get1 = self.get.clone();
        let get1_for_set = get1.clone();
        let set1 = self.set.clone();
        let get2 = other.get.clone();
        let set2 = other.set.clone();

        let get_fn = move |s| get2.call(get1.call(s));
        let set_fn = move |s: S, b| {
            let a = get1_for_set.call(s.clone());
            let new_a = set2.call((a, b));
            set1.call((s, new_a))
        };

        Lens::new(get_fn, set_fn)
    }

    /// Creates a lens for a field.
    ///
    /// # Arguments
    ///
    /// * `get` - A function to get the value of the field.
    /// * `set` - A function to set the value of the field.
    ///
    /// # Returns
    ///
    /// A new lens for the field.
    pub fn field<B: TypeConstraints>(
        get: impl Fn(&A) -> &B + Clone + Send + Sync + 'static,
        set: impl Fn(A, B) -> A + Clone + Send + Sync + 'static,
    ) -> Lens<A, B> {
        Lens::new(
            move |a: A| get(&a).clone(),
            move |a: A, b: B| set(a, b),
        )
    }
}

impl<S: TypeConstraints, A: TypeConstraints> HKT for Lens<S, A> {
    type Output<T> = Lens<S, T> where T: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Composable<A> for Lens<S, A> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<A, U> + Clone,
    {
        let get1 = self.get.clone();
        let set1 = self.set.clone();
        let f = f.clone();
        let get2 = get1.clone();

        Lens {
            get: FnType::new(move |s| {
                f.call(get1.call(s))
            }),
            set: FnType::new(move |(s, _u): (S, U)| {
                let a = get2.call(s.clone());
                set1.call((s, a))
            }),
        }
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Identity<A> for Lens<S, A> {
    fn identity() -> Self::Output<A> {
        Lens::new(
            |_s| A::default(),
            |s, _| s,
        )
    }

    fn map_identity<B, F>(f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        Lens::new(
            move |_s| f.call(A::default()),
            |s, _| s,
        )
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Category<A> for Lens<S, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Arrow<A, A> for Lens<S, A> {}