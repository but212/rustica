use std::fmt::Debug;
use crate::fntype::SendSyncFn;
use crate::category::hkt::ReturnTypeConstraints;

/// A lens that focuses on a field of a struct.
/// 
/// A `Lens` provides a functional way to focus on a specific field of a struct.
/// It allows you to get, set, and modify the value of that field, as well as compose
/// with other lenses to create more complex lenses.
///
/// #Laws
/// A `Lens` must satisfy these laws:
/// 1. GetSet (Get-Set Law): `lens.get(&lens.set(s, a)) = a`
/// 2. SetGet (Set-Get Law): `lens.set(s, lens.get(&s)) = s`
/// 3. SetSet (Set-Set Law): `lens.set(lens.set(s, a1), a2) = lens.set(s, a2)`
/// 4. Composition: For lenses l1 and l2:
///    - `(l1.compose(l2)).get(s) = l2.get(&l1.get(&s))`
///    - `(l1.compose(l2)).set(s, c) = l1.set(s, l2.set(l1.get(&s), c))`
/// 5. Identity: For any lens l:
///    - `l.compose(identity()) = l`
///    - `identity().compose(l) = l`
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    // Fields to store the `get` and `set` functions.
    get: SendSyncFn<S, A>,
    set: SendSyncFn<(S, A), S>,
}

impl<S, A> Lens<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
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
            get: SendSyncFn::new(get),
            set: SendSyncFn::new(move |args: (S, A)| set(args.0, args.1)),
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
        let f = SendSyncFn::new(f);
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
        B: ReturnTypeConstraints,
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
        B: ReturnTypeConstraints,
    {
        Lens::new(get, set)
    }
}
