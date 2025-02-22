use std::sync::Arc;
use crate::prelude::*;

/// A lens that focuses on a field of a struct.
/// 
/// A `Lens<S, A>` provides a way to view or modify a part `A` of a larger structure `S`.
/// It consists of a getter function that extracts `A` from `S`, and a setter function
/// that updates `A` within `S`.
/// 
/// # Type Parameters
/// 
/// * `S`: The type of the whole structure.
/// * `A`: The type of the part being focused on.
/// 
/// # Examples
///
/// ```
/// use rustica::datatypes::lens::Lens;
///
/// #[derive(Default, Eq, PartialEq, Debug, Clone)]
/// struct Person {
///     name: String,
///     age: u32,
/// }
///
/// let name_lens = Lens::new(
///     |p: Person| p.name.clone(),
///     |mut p, name| { p.name = name; p }
/// );
///
/// let age_lens = Lens::new(
///     |p: Person| p.age,
///     |mut p, age| { p.age = age; p }
/// );
///
/// let person = Person { name: "Alice".to_string(), age: 30 };
///
/// // Get the name
/// assert_eq!(name_lens.get(person.clone()), "Alice");
///
/// // Modify the age
/// let older_person = age_lens.modify(person.clone(), |age| age + 1);
/// assert_eq!(older_person.age, 31);
///
/// // Set a new name
/// let renamed_person = name_lens.set(person, "Bob".to_string());
/// assert_eq!(renamed_person.name, "Bob");
///
/// // Compose lenses
/// let first_char_lens = Lens::new(
///     |s: String| s.chars().next().unwrap_or_default(),
///     |mut s, c| { s.replace_range(0..1, &c.to_string()); s }
/// );
///
/// let first_char_of_name_lens = name_lens.compose_lens(&first_char_lens);
/// let person = Person { name: "Alice".to_string(), age: 30 };
/// assert_eq!(first_char_of_name_lens.get(person.clone()), 'A');
///
/// let modified_person = first_char_of_name_lens.set(person, 'B');
/// assert_eq!(modified_person.name, "Blice");
/// ```
#[derive(Clone)]
pub struct Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    /// The getter function that extracts `A` from `S`.
    get: Arc<dyn Fn(S) -> A + Send + Sync>,
    /// The setter function that updates `A` within `S`.
    set: Arc<dyn Fn(S, A) -> S + Send + Sync>,
}

impl<S, A> Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    /// Creates a new lens.
    ///
    /// # Arguments
    ///
    /// * `get` - A function to get the value of the field.
    /// * `set` - A function to set the value of the field.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The type of the getter function.
    /// * `H`: The type of the setter function.
    pub fn new<G, H>(get: G, set: H) -> Self
    where
        G: Fn(S) -> A + Clone + Send + Sync + 'static,
        H: Fn(S, A) -> S + Clone + Send + Sync + 'static,
    {
        Lens {
            get: Arc::new(get),
            set: Arc::new(set),
        }
    }

    /// Gets the field value from the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct to get the field value from.
    ///
    /// # Returns
    ///
    /// The value of the field.
    pub fn get(&self, s: S) -> A {
        (self.get)(s)
    }

    /// Sets the field value in the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct to update.
    /// * `a` - The new value for the field.
    ///
    /// # Returns
    ///
    /// A new struct with the updated field value.
    pub fn set(&self, s: S, a: A) -> S {
        (self.set)(s, a)
    }

    /// Modifies the field value in the struct.
    ///
    /// # Arguments
    ///
    /// * `s` - The struct to modify.
    /// * `f` - A function that takes the current field value and returns a new value.
    ///
    /// # Returns
    ///
    /// A new struct with the modified field value.
    pub fn modify(&self, s: S, f: impl Fn(A) -> A + 'static) -> S {
        let a = self.get(s.clone());
        self.set(s, f(a))
    }

    /// Composes this lens with another lens.
    ///
    /// # Arguments
    ///
    /// * `other` - Another lens to compose with this one.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type that the other lens focuses on.
    ///
    /// # Returns
    ///
    /// A new lens that focuses on `B` through `S` and `A`.
    pub fn compose_lens<B>(&self, other: &Lens<A, B>) -> Lens<S, B>
    where
        B: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    {
        let self_get = Arc::clone(&self.get);
        let self_set = Arc::clone(&self.set);
        let other_get = Arc::clone(&other.get);
        let other_set = Arc::clone(&other.set);
        
        Lens::new(
            {
                let self_get = Arc::clone(&self_get);
                let other_get = Arc::clone(&other_get);
                move |s| other_get(self_get(s))
            },
            {
                let self_get = Arc::clone(&self_get);
                let self_set = Arc::clone(&self_set);
                let other_set = Arc::clone(&other_set);
                move |s, b| self_set(s.clone(), other_set(self_get(s), b))
            }
        )
    }
}

impl<S, A> TypeOps for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn clone_box(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn equals(&self, _other: &AnyBox) -> bool {
        // Lenses can't be compared for equality since they contain functions
        false
    }
}

impl<S, A> HKT for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn apply_type(&self) -> AnyBox {
        self.clone_box()
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Lens<S, A>>().map(|x| x.clone_box())
    }
}

impl<S, A> Identity for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn identity() -> AnyBox {
        Arc::new(Lens::new(
            |s: S| s,
            |_s: S, a: S| a
        )) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let f1 = Arc::clone(&f);
        let f2 = Arc::clone(&f);
        Arc::new(Lens::new(
            move |s: S| {
                if let Some(result) = f1(Arc::new(s.clone()) as AnyBox).downcast_ref::<S>() {
                    result.clone()
                } else {
                    S::default()
                }
            },
            move |_s: S, a: S| {
                if let Some(result) = f2(Arc::new(a.clone()) as AnyBox).downcast_ref::<S>() {
                    result.clone()
                } else {
                    S::default()
                }
            }
        )) as AnyBox
    }
}

impl<S, A> Arrow for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let f1 = Arc::clone(func);
            let f2 = Arc::clone(func);
            Arc::new(Lens::new(
                move |s: S| {
                    if let Some(result) = f1(Arc::new(s.clone()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                },
                move |s: S, _a: A| {
                    if let Some(result) = f2(Arc::new(s.clone()) as AnyBox).downcast_ref::<S>() {
                        result.clone()
                    } else {
                        s
                    }
                }
            )) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let f1 = Arc::clone(func);
            let f2 = Arc::clone(func);
            Arc::new(Lens::new(
                move |s: S| {
                    if let Some(result) = f1(Arc::new(s.clone()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                },
                move |s: S, _a: A| {
                    if let Some(result) = f2(Arc::new(s.clone()) as AnyBox).downcast_ref::<S>() {
                        result.clone()
                    } else {
                        s
                    }
                }
            )) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        self.first(f)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        if let (Some(f), Some(g)) = (
            f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>(),
            g.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>()
        ) {
            let f = Arc::clone(f);
            let g = Arc::clone(g);
            Arc::new(Lens::new(
                move |s: S| {
                    if let Some(result) = f(Arc::new(s.clone()) as AnyBox).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                },
                move |s: S, _a: A| {
                    if let Some(result) = g(Arc::new(s.clone()) as AnyBox).downcast_ref::<S>() {
                        result.clone()
                    } else {
                        s
                    }
                }
            )) as AnyBox
        } else {
            self.clone_box()
        }
    }
}

impl<S, A> Composable for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn compose(
        &self,
        g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        let g = g.clone();
        let f = f.clone();
        Arc::new(move |x: AnyBox| -> AnyBox {
            g(f(x))
        })
    }

    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        let f1 = Arc::clone(&f);
        let f2 = Arc::clone(&f);
        Arc::new(Lens::new(
            move |s: S| {
                if let Some(result) = f1(Arc::new(get(s.clone())) as AnyBox).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| {
                if let Some(result) = f2(Arc::new(set(s.clone(), a.clone())) as AnyBox).downcast_ref::<S>() {
                    result.clone()
                } else {
                    s
                }
            }
        )) as AnyBox
    }
}

impl<S, A> Functor for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        let f = Arc::clone(&f);
        Arc::new(Lens::new(
            move |s: S| {
                let s = s.clone();
                let a = get(s);
                if let Some(result) = f(Arc::new(a) as AnyBox).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| set(s, a)
        )) as AnyBox
    }
}

impl<S, A> Pure for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn pure(value: AnyBox) -> AnyBox {
        if let Some(a) = value.downcast_ref::<A>() {
            let value = a.clone();
            Arc::new(Lens::new(
                move |_: S| value.clone(),
                move |s: S, _: A| s
            )) as AnyBox
        } else {
            Arc::new(Lens::new(
                move |_: S| A::default(),
                move |s: S, _: A| s
            )) as AnyBox
        }
    }
}

impl<S, A> Monad for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        let f = Arc::clone(&f);
        Arc::new(Lens::new(
            move |s: S| {
                let s = s.clone();
                let a = get(s.clone());
                if let Some(lens_b) = f(Arc::new(a) as AnyBox).downcast_ref::<Lens<S, A>>() {
                    (lens_b.get)(s)
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| set(s, a)
        )) as AnyBox
    }

    fn join(&self) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        Arc::new(Lens::new(
            move |s: S| {
                let s = s.clone();
                let inner = get(s.clone());
                if let Some(lens) = (Arc::new(inner) as AnyBox).downcast_ref::<Lens<S, A>>() {
                    (lens.get)(s)
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| set(s, a)
        )) as AnyBox
    }
}

impl<S, A> Bifunctor for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        let f = Arc::clone(&f);
        let g = Arc::clone(&g);
        Arc::new(Lens::new(
            move |s: S| {
                let s = s.clone();
                let a = get(s);
                if let Some(result) = g(Arc::new(a) as AnyBox).downcast_ref::<A>() {
                    result.clone()
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| {
                let result = set(s.clone(), a);
                if let Some(new_s) = f(Arc::new(result) as AnyBox).downcast_ref::<S>() {
                    new_s.clone()
                } else {
                    s
                }
            }
        )) as AnyBox
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(f, Arc::new(|x| x))
    }

    fn map_second(&self, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(Arc::new(|x| x), g)
    }
}

impl<S, A> Category for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_lens) = other.downcast_ref::<Lens<A, S>>() {
            Arc::new(self.compose_lens(other_lens)) as AnyBox
        } else {
            self.clone_box()
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Lens::new(
            |s: S| s,
            |_s: S, a: S| a
        )) as AnyBox
    }
}

impl<S, A> Applicative for Lens<S, A>
where
    S: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
    A: TypeOps + Clone + Default + Send + Sync + PartialEq + 'static,
{
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        Arc::new(Lens::new(
            move |s: S| {
                let s = s.clone();
                let a = get(s.clone());
                let a_box = Arc::new(a) as AnyBox;
                let result = f(a_box);
                if let Some(a) = result.downcast_ref::<A>() {
                    a.clone()
                } else {
                    A::default()
                }
            },
            move |s: S, a: A| {
                set(s, a)
            }
        )) as AnyBox
    }

    fn lift2(&self, b: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(lens_b) = b.downcast_ref::<Lens<S, A>>() {
            let get1 = Arc::clone(&self.get);
            let get2 = Arc::clone(&lens_b.get);
            let set1 = Arc::clone(&self.set);
            let set2 = Arc::clone(&lens_b.set);
            let f = Arc::clone(&f);
            Arc::new(Lens::new(
                move |s: S| {
                    let s = s.clone();
                    if let Some(result) = f(
                        Arc::new(get1(s.clone())) as AnyBox,
                        Arc::new(get2(s)) as AnyBox
                    ).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                },
                move |s: S, a: A| {
                    let s2 = set1(s.clone(), a.clone());
                    set2(s2, a)
                }
            )) as AnyBox
        } else {
            Self::identity()
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(lens_b), Some(lens_c)) = (b.downcast_ref::<Lens<S, A>>(), c.downcast_ref::<Lens<S, A>>()) {
            let get1 = Arc::clone(&self.get);
            let get2 = Arc::clone(&lens_b.get);
            let get3 = Arc::clone(&lens_c.get);
            let set1 = Arc::clone(&self.set);
            let set2 = Arc::clone(&lens_b.set);
            let set3 = Arc::clone(&lens_c.set);
            let f = Arc::clone(&f);
            Arc::new(Lens::new(
                move |s: S| {
                    let s = s.clone();
                    if let Some(result) = f(
                        Arc::new(get1(s.clone())) as AnyBox,
                        Arc::new(get2(s.clone())) as AnyBox,
                        Arc::new(get3(s)) as AnyBox
                    ).downcast_ref::<A>() {
                        result.clone()
                    } else {
                        A::default()
                    }
                },
                move |s: S, a: A| {
                    let s2 = set1(s.clone(), a.clone());
                    let s3 = set2(s2, a.clone());
                    set3(s3, a)
                }
            )) as AnyBox
        } else {
            Self::identity()
        }
    }
}
