#![doc = include_str!("../../docs/datatypes/lens.md")]

use core::fmt;
use core::marker::PhantomData;

/// A `Lens` is a first-class reference to a subpart of some data type.
///
/// It provides a way to view, modify and transform a part of a larger structure.
///
/// # Type Parameters
///
/// * `S` - The type of the whole structure
/// * `A` - The type of the part being focused on
/// * `ViewFn` - The closure type for inspecting a focus: `Fn(&S) -> &A`
/// * `SetFn` - The closure type for updating a structure: `Fn(S, A) -> S`
pub struct Lens<S, A, ViewFn, SetFn> {
    view: ViewFn,
    set: SetFn,
    _phantom: PhantomData<fn(S) -> A>,
}

impl<S, A, ViewFn, SetFn> Clone for Lens<S, A, ViewFn, SetFn>
where
    ViewFn: Clone,
    SetFn: Clone,
{
    fn clone(&self) -> Self {
        Lens {
            view: self.view.clone(),
            set: self.set.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<S, A, ViewFn, SetFn> fmt::Debug for Lens<S, A, ViewFn, SetFn> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lens").finish_non_exhaustive()
    }
}

impl<S, A, ViewFn, SetFn> Lens<S, A, ViewFn, SetFn>
where
    ViewFn: Fn(&S) -> &A,
    SetFn: Fn(S, A) -> S,
{
    /// Creates a new reference-borrowing lens from view and setter closures.
    ///
    /// # Arguments
    ///
    /// * `view` - A closure borrowing the focused part from the whole: `Fn(&S) -> &A`
    /// * `set` - A closure updating the whole structure with a new focus: `Fn(S, A) -> S`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Point { x: f64, y: f64 }
    ///
    /// let x_lens = Lens::new(
    ///     |p: &Point| &p.x,
    ///     |p: Point, x: f64| Point { x, ..p },
    /// );
    ///
    /// let point = Point { x: 2.0, y: 3.0 };
    /// assert_eq!(*x_lens.view(&point), 2.0);
    /// ```
    #[inline]
    pub const fn new(view: ViewFn, set: SetFn) -> Self {
        Lens {
            view,
            set,
            _phantom: PhantomData,
        }
    }

    /// Views the focused part of a structure as a reference with zero allocations.
    #[inline]
    pub fn view<'s>(&self, source: &'s S) -> &'s A {
        (self.view)(source)
    }

    /// Extracts an owned clone of the focused part, adhering to `C-CONV` conventions.
    #[inline]
    pub fn to_value(&self, source: &S) -> A
    where
        A: Clone,
    {
        (self.view)(source).clone()
    }

    /// Legacy getter extracting an owned clone of the focused part.
    ///
    /// Deprecated in 0.20.0 in favor of [`Lens::view`] (0 B reference) or
    /// [`Lens::to_value`] (explicit owned extraction per C-CONV).
    #[deprecated(
        since = "0.20.0",
        note = "Use lens.view(&s) for 0-allocation borrowed access, or lens.to_value(&s) for owned extraction per C-CONV"
    )]
    #[inline]
    pub fn get(&self, source: &S) -> A
    where
        A: Clone,
    {
        self.to_value(source)
    }

    /// Sets the focused part with zero-allocation short-circuiting when `A: PartialEq`.
    ///
    /// If the new value equals the current value under `PartialEq`, returns `source` untouched (0 B, 0 clones).
    /// If values differ, constructs an updated structure via `set`.
    ///
    /// Note: Equality check uses `PartialEq`. For bit-exact preservation (such as distinguishing `-0.0` and `0.0`
    /// on `f64`) or non-reflexive types (`NaN`), use [`Lens::set_always`].
    #[inline]
    pub fn set(&self, source: S, value: A) -> S
    where
        A: PartialEq,
    {
        if (self.view)(&source) == &value {
            source
        } else {
            (self.set)(source, value)
        }
    }

    /// Sets the focused part unconditionally without equality checking.
    #[inline]
    pub fn set_always(&self, source: S, value: A) -> S {
        (self.set)(source, value)
    }

    /// Modifies the focused part with single-clone and zero-allocation short-circuiting.
    ///
    /// Clones `current` exactly 1 time to pass owned value to `f(current)`.
    /// If `f` returns an identical value under `PartialEq`, returns `source` untouched (0 B).
    ///
    /// Note: Equality check uses `PartialEq`. For bit-exact types or non-reflexive types,
    /// use [`Lens::modify_always`].
    #[inline]
    pub fn modify<F>(&self, source: S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        A: Clone + PartialEq,
    {
        let current = (self.view)(&source);
        let new_value = f(current.clone());
        if current == &new_value {
            source
        } else {
            (self.set)(source, new_value)
        }
    }

    /// Modifies the focused part unconditionally.
    #[inline]
    pub fn modify_always<F>(&self, source: S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        A: Clone,
    {
        let new_value = f((self.view)(&source).clone());
        (self.set)(source, new_value)
    }
}

#[inline]
fn compose_lens_views<S, A: 'static, B, V1, V2>(v1: V1, v2: V2) -> impl Fn(&S) -> &B + Clone
where
    V1: Fn(&S) -> &A + Clone,
    V2: Fn(&A) -> &B + Clone,
{
    move |s: &S| v2(v1(s))
}

impl<S, A, ViewFn, SetFn> Lens<S, A, ViewFn, SetFn>
where
    ViewFn: Fn(&S) -> &A + Clone,
    SetFn: Fn(S, A) -> S + Clone,
{
    /// Composes two lenses to create a new lens that focuses on a nested structure.
    ///
    /// Given a lens from `S` to `A` and a lens from `A` to `B`, this creates a new
    /// lens from `S` to `B` with zero-allocation reference view preservation.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn then<B, ViewFn2, SetFn2>(
        self, other: Lens<A, B, ViewFn2, SetFn2>,
    ) -> Lens<S, B, impl Fn(&S) -> &B + Clone, impl Fn(S, B) -> S + Clone>
    where
        A: Clone + 'static,
        ViewFn2: Fn(&A) -> &B + Clone,
        SetFn2: Fn(A, B) -> A + Clone,
    {
        let view1 = self.view;
        let view2 = other.view;
        let set1 = self.set;
        let set2 = other.set;

        let view1_for_set = view1.clone();

        Lens {
            view: compose_lens_views(view1, view2),
            set: move |s: S, b: B| {
                let current_a = view1_for_set(&s).clone();
                let updated_a = set2(current_a, b);
                set1(s, updated_a)
            },
            _phantom: PhantomData,
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use alloc::rc::Rc;
    use alloc::string::String;

    use super::Lens;

    #[derive(Clone, Debug, PartialEq)]
    struct Address {
        street: String,
        city: String,
    }

    #[derive(Clone, Debug, PartialEq)]
    struct Person {
        name: String,
        address: Rc<Address>,
    }

    #[derive(Clone, Debug, PartialEq)]
    struct Point {
        x: f64,
        y: f64,
    }

    #[allow(clippy::type_complexity)]
    fn street_lens() -> Lens<
        Address,
        String,
        impl Fn(&Address) -> &String + Clone,
        impl Fn(Address, String) -> Address + Clone,
    > {
        Lens::new(|a: &Address| &a.street, |a, street| Address { street, ..a })
    }

    #[allow(clippy::type_complexity)]
    fn address_lens() -> Lens<
        Person,
        Rc<Address>,
        impl Fn(&Person) -> &Rc<Address> + Clone,
        impl Fn(Person, Rc<Address>) -> Person + Clone,
    > {
        Lens::new(
            |p: &Person| &p.address,
            |p, address| Person { address, ..p },
        )
    }

    fn x_lens()
    -> Lens<Point, f64, impl Fn(&Point) -> &f64 + Clone, impl Fn(Point, f64) -> Point + Clone> {
        Lens::new(|p: &Point| &p.x, |p, x| Point { x, ..p })
    }

    #[test]
    fn test_modify_move_closure() {
        struct MoveOnly(String);
        let move_only = MoveOnly("suffix".into());

        #[derive(Clone, Debug, PartialEq)]
        struct Item {
            name: String,
        }
        let item_lens = Lens::new(|i: &Item| &i.name, |_i, name| Item { name });

        let item = Item {
            name: "prefix_".into(),
        };
        let updated = item_lens.modify(item, move |mut s| {
            s.push_str(&move_only.0);
            s
        });
        assert_eq!(updated.name, "prefix_suffix");
    }

    #[test]
    fn test_lens_clonable_without_target_clone() {
        struct NonCloneStruct {
            val: u32,
        }
        let lens = Lens::new(
            |s: &NonCloneStruct| &s.val,
            |_s, val| NonCloneStruct { val },
        );
        let cloned = lens.clone();
        let s = NonCloneStruct { val: 42 };
        assert_eq!(*cloned.view(&s), 42);
        assert_eq!(cloned.to_value(&s), 42);
    }

    #[test]
    fn test_set_always_bypasses_equality_check() {
        let address = Rc::new(Address {
            street: "Main St".into(),
            city: "Metropolis".into(),
        });
        let person = Person {
            name: "Bob".into(),
            address: Rc::clone(&address),
        };
        let lens = address_lens();

        let same = lens.set(person.clone(), Rc::clone(&address));
        assert!(Rc::ptr_eq(&person.address, &same.address));

        let force_new = lens.set_always(person.clone(), Rc::new((*address).clone()));
        assert!(!Rc::ptr_eq(&person.address, &force_new.address));
    }

    #[test]
    fn nested_updates_preserve_sharing_when_unchanged() {
        let person = Person {
            name: "Alice".into(),
            address: Rc::new(Address {
                street: "123 Main St".into(),
                city: "Springfield".into(),
            }),
        };
        let lens = address_lens();
        let unchanged = lens.modify(person.clone(), |address| {
            street_lens().set((*address).clone(), "123 Main St".into());
            address
        });
        assert!(Rc::ptr_eq(&person.address, &unchanged.address));
    }

    #[test]
    #[allow(deprecated)]
    fn composition_and_unconditional_updates_work() {
        let person = Person {
            name: "Alice".into(),
            address: Rc::new(Address {
                street: "123 Main St".into(),
                city: "Springfield".into(),
            }),
        };
        let address_val_lens = Lens::new(
            |p: &Person| p.address.as_ref(),
            |p, address| Person {
                address: Rc::new(address),
                ..p
            },
        );
        let composed = address_val_lens.then(street_lens());
        assert_eq!(composed.view(&person), "123 Main St");
        assert_eq!(composed.to_value(&person), "123 Main St");
        assert_eq!(composed.get(&person), "123 Main St");

        let point = Point { x: 10.0, y: 20.0 };
        assert_eq!(x_lens().set_always(point.clone(), 10.0).x, 10.0);
        assert_eq!(x_lens().modify_always(point, |x| x).x, 10.0);
    }
}
