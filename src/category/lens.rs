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
/// use rustica::category::lens::Lens;
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
pub struct Lens<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    // Fields to store the `get` and `set` functions.
    get: FnType<S, A>,
    set: FnType<(S, A), S>,
}

impl<S, A> Lens<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    /// Creates a new lens.
    ///
    /// # Arguments
    ///
    /// * `get` - A function to get the value of the field.
    /// * `set` - A function to set the value of the field.
    pub fn new<G, H>(get: G, set: H) -> Self
    where
        G: Fn(S) -> A + Send + Sync + 'static,
        H: Fn(S, A) -> S + Send + Sync + 'static,
    {
        Lens {
            get: FnType::new(get),
            set: FnType::new(move |args: (S, A)| set(args.0, args.1)),
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
        F: Fn(A) -> A + Send + Sync + 'static,
    {
        let a = self.get(&s);
        let f = FnType::new(f);
        self.set(s, f.call(a))
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
    pub fn compose<B>(self, other: Lens<A, B>) -> Lens<S, B>
    where
        B: TypeConstraints,
    {
        Lens::new(
            {
                let self_clone = self.clone();
                let other_clone = other.clone();
                move |s: S| other_clone.get(&self_clone.get(&s))
            },
            {
                let self_clone = self.clone();
                let other_clone = other.clone();
                move |s: S, b: B| {
                    let a = self_clone.get(&s);
                    self_clone.set(s, other_clone.set(a, b))
                }
            },
        )
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
    pub fn field<B>(get: impl Fn(A) -> B + Send + Sync + 'static, set: impl Fn(A, B) -> A + Send + Sync + 'static) -> Lens<A, B>
    where
        B: TypeConstraints,
    {
        Lens::new(get, set)
    }
}

impl<S, A> HKT for Lens<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    type Output<T> = Lens<S, T> where T: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Composable for Lens<S, A> {}

impl<S: TypeConstraints, A: TypeConstraints> Identity for Lens<S, A> {}

impl<S: TypeConstraints, A: TypeConstraints> Category for Lens<S, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;

    fn identity_morphism<B: TypeConstraints>() -> Self::Morphism<B, B> {
        FnType::new(|x| x)
    }

    fn compose_morphisms<B, C, D>(f: Self::Morphism<B, C>, g: Self::Morphism<C, D>) -> Self::Morphism<B, D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Arrow for Lens<S, A> {
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<B, C>,
    {
        FnType::new(move |x: B| f.call(x))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        Self::arrow(FnType::new(move |(b, d): (B, D)| (f.call(b), d)))
    }
}