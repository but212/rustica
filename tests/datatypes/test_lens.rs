use quickcheck_macros::quickcheck;
use rustica::datatypes::lens::Lens;
use std::cell::Cell;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestPerson {
    name: String,
    age: u32,
}

fn name_lens() -> Lens<
    TestPerson,
    String,
    impl Fn(&TestPerson) -> String,
    impl Fn(TestPerson, String) -> TestPerson,
> {
    Lens::new(
        |p: &TestPerson| p.name.clone(),
        |p, name| TestPerson { name, ..p },
    )
}

fn age_lens()
-> Lens<TestPerson, u32, impl Fn(&TestPerson) -> u32, impl Fn(TestPerson, u32) -> TestPerson> {
    Lens::new(|p: &TestPerson| p.age, |p, age| TestPerson { age, ..p })
}

// Law 1: GetSet Law (l.set(s.clone(), l.get(&s)) == s)
#[test]
fn test_lens_get_set_law() {
    let lens = name_lens();
    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };
    assert_eq!(lens.set(person.clone(), lens.get(&person)), person);
}

// Law 2: SetGet Law (l.get(&l.set(s, v)) == v)
#[quickcheck]
fn test_lens_set_get_law(age: u32) -> bool {
    let lens = age_lens();
    let person = TestPerson {
        name: "Bob".into(),
        age: 20,
    };
    lens.get(&lens.set(person, age)) == age
}

// Law 3: SetSet Law (l.set(l.set(s, v1), v2) == l.set(s, v2))
#[quickcheck]
fn test_lens_set_set_law(v1: u32, v2: u32) -> bool {
    let lens = age_lens();
    let person = TestPerson {
        name: "Charlie".into(),
        age: 10,
    };
    lens.set(lens.set(person.clone(), v1), v2) == lens.set(person, v2)
}

// Contract C-01: Lens works on non-Clone structs and fields
#[test]
fn test_lens_non_clone_struct() {
    struct NonClonePerson {
        id: u64,
    }

    let id_lens = Lens::new(|p: &NonClonePerson| p.id, |_p, id| NonClonePerson { id });

    let p = NonClonePerson { id: 42 };
    assert_eq!(id_lens.get(&p), 42);

    let updated = id_lens.set_always(p, 99);
    assert_eq!(id_lens.get(&updated), 99);

    let modified = id_lens.modify_always(updated, |id| id + 1);
    assert_eq!(id_lens.get(&modified), 100);
}

#[test]
fn test_modify_supports_non_clone_partial_eq_focus() {
    #[derive(PartialEq)]
    struct Focus(u8);

    let lens = Lens::new(|source: &u8| Focus(*source), |_source, Focus(value)| value);
    assert_eq!(lens.modify(41, |Focus(value)| Focus(value + 1)), 42);
}

#[test]
fn test_modify_applies_transform_once() {
    let lens = name_lens();
    let transform_count = Cell::new(0);
    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };

    let updated = lens.modify(person, |name| {
        transform_count.set(transform_count.get() + 1);
        format!("Dr. {name}")
    });

    assert_eq!(updated.name, "Dr. Alice");
    assert_eq!(transform_count.get(), 1);
}

// Contract C-03: Structural sharing preservation when unchanged
#[test]
fn test_modify_preserves_instance_when_unchanged() {
    #[derive(Clone, Debug, PartialEq)]
    struct Node {
        label: String,
        payload: Rc<String>,
    }

    let payload_lens = Lens::new(
        |n: &Node| n.payload.clone(),
        |n, payload| Node { payload, ..n },
    );

    let original = Node {
        label: "root".into(),
        payload: Rc::new("immutable-data".into()),
    };

    let unchanged = payload_lens.modify(original.clone(), |p| p);
    assert!(Rc::ptr_eq(&original.payload, &unchanged.payload));

    let same_set = payload_lens.set(original.clone(), original.payload.clone());
    assert!(Rc::ptr_eq(&original.payload, &same_set.payload));
}

// Contract C-05: Closure-based Lens implements Debug
#[test]
fn test_lens_debug_formatting() {
    let lens = Lens::new(|p: &TestPerson| p.age, |p, age| TestPerson { age, ..p });
    let debug_output = format!("{:?}", lens);
    assert!(debug_output.contains("Lens"));
}

// Composition and Chaining
#[test]
fn test_lens_composition_and_chaining() {
    #[derive(Clone, Debug, PartialEq)]
    struct ZipCode {
        code: u32,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Address {
        city: String,
        zip: ZipCode,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Company {
        address: Address,
    }

    let company_address_lens = Lens::new(
        |c: &Company| c.address.clone(),
        |_c, address| Company { address },
    );
    let address_city_lens = Lens::new(
        |a: &Address| a.city.clone(),
        |a, city| Address { city, ..a },
    );
    let address_zip_lens = Lens::new(|a: &Address| a.zip.clone(), |a, zip| Address { zip, ..a });
    let zip_code_lens = Lens::new(|z: &ZipCode| z.code, |_z, code| ZipCode { code });

    // 2-level composition
    let company_city_lens = company_address_lens.clone().then(address_city_lens);

    let company = Company {
        address: Address {
            city: "Metropolis".into(),
            zip: ZipCode { code: 10001 },
        },
    };

    assert_eq!(company_city_lens.get(&company), "Metropolis");
    let moved = company_city_lens.set(company.clone(), "Gotham".into());
    assert_eq!(moved.address.city, "Gotham");

    // Verification of Contract C-03: Composed lens cloneability
    let cloned_lens = company_city_lens.clone();
    assert_eq!(cloned_lens.get(&moved), "Gotham");

    // Verification of Contract C-02: Multi-level (3-level) composition chaining without heap allocation
    let company_zip_code_lens = company_address_lens
        .then(address_zip_lens)
        .then(zip_code_lens);

    assert_eq!(company_zip_code_lens.get(&company), 10001);
    let rezipped = company_zip_code_lens.set(company, 90210);
    assert_eq!(rezipped.address.zip.code, 90210);
}

#[test]
fn test_iso_map_then_composition() {
    #[derive(Clone, Debug, PartialEq)]
    struct Inner {
        value: u32,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Outer {
        inner: Inner,
    }

    let outer_inner = Lens::new(|o: &Outer| o.inner.clone(), |_o, inner| Outer { inner });
    let inner_val = Lens::new(|i: &Inner| i.value, |_i, value| Inner { value });

    let mapped = outer_inner.iso_map(|i: Inner| i, |i: Inner| i);
    let composed = mapped.then(inner_val);

    let outer = Outer {
        inner: Inner { value: 42 },
    };

    assert_eq!(composed.get(&outer), 42);
    let updated = composed.set(outer, 100);
    assert_eq!(updated.inner.value, 100);

    let cloned = composed.clone();
    assert_eq!(cloned.get(&updated), 100);
}

// Slice 1: Contract C-01 & Law L-01
#[test]
fn test_lens_from_view_basic() {
    let lens = Lens::from_view(|p: &TestPerson| &p.name, |p, name| TestPerson { name, ..p });
    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };

    // Contract C-01: view returns reference without clone
    assert_eq!(lens.view(&person), "Alice");

    // Law L-01: *view(&s) == get(&s)
    assert_eq!(*lens.view(&person), lens.get(&person));
}

// Slice 2: Contract C-03 & C-05 & Law L-02
thread_local! {
    static CLONES: Cell<usize> = const { Cell::new(0) };
}

#[derive(PartialEq, Debug)]
struct Tracked(u32);

impl Clone for Tracked {
    fn clone(&self) -> Self {
        CLONES.with(|c| c.set(c.get() + 1));
        Tracked(self.0)
    }
}

#[derive(Clone, PartialEq, Debug)]
struct TrackedContainer {
    item: Tracked,
    id: u64,
}

#[derive(Clone, PartialEq, Debug)]
struct RcContainer {
    payload: Rc<String>,
}

#[test]
fn test_from_view_set_preserves_sharing() {
    let lens = Lens::from_view(
        |c: &TrackedContainer| &c.item,
        |c, item| TrackedContainer { item, ..c },
    );
    let container = TrackedContainer {
        item: Tracked(42),
        id: 1,
    };

    // Contract C-03 & Law L-02: Zero-clone set on same value
    let c = container.clone();
    CLONES.with(|cnt| cnt.set(0));
    let same = lens.set(c, Tracked(42));
    assert_eq!(
        CLONES.with(|cnt| cnt.get()),
        0,
        "set on unchanged value must perform 0 clones"
    );
    assert_eq!(same.item, Tracked(42));

    // Contract C-05: Exactly 1 clone on modify identity (0 for comparison)
    let c2 = container.clone();
    CLONES.with(|cnt| cnt.set(0));
    let same_mod = lens.modify(c2, |x| x);
    assert_eq!(
        CLONES.with(|cnt| cnt.get()),
        1,
        "modify on unchanged value must perform exactly 1 clone for f(current)"
    );
    assert_eq!(same_mod.item, Tracked(42));

    // Pointer equality preservation
    let rc_lens = Lens::from_view(
        |c: &RcContainer| &c.payload,
        |_c, payload| RcContainer { payload },
    );
    let rc_c = RcContainer {
        payload: Rc::new("immutable-data".into()),
    };
    let same_rc = rc_lens.set(rc_c.clone(), Rc::clone(&rc_c.payload));
    assert!(Rc::ptr_eq(&rc_c.payload, &same_rc.payload));

    let same_rc_mod = rc_lens.modify(rc_c.clone(), |p| p);
    assert!(Rc::ptr_eq(&rc_c.payload, &same_rc_mod.payload));

    // Mutation path verification
    let c3 = container.clone();
    let updated = lens.set(c3, Tracked(7));
    assert_eq!(updated.item, Tracked(7));
    assert_eq!(updated.id, 1, "unrelated field must be preserved");

    let c4 = container.clone();
    let mod_updated = lens.modify(c4, |x| Tracked(x.0 + 10));
    assert_eq!(mod_updated.item, Tracked(52));
    assert_eq!(mod_updated.id, 1, "unrelated field must be preserved");
}

// Slice 3: Contract C-04, C-06, C-07 & Law L-03
#[test]
fn test_from_view_composed_view() {
    #[derive(Clone, Debug, PartialEq)]
    struct ZipCode {
        code: Tracked,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Address {
        city: String,
        zip: ZipCode,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Company {
        name: String,
        address: Address,
    }

    let company_lens = Lens::from_view(
        |c: &Company| &c.address,
        |c, address| Company { address, ..c },
    );
    let address_zip_lens = Lens::from_view(|a: &Address| &a.zip, |a, zip| Address { zip, ..a });
    let zip_code_lens = Lens::from_view(|z: &ZipCode| &z.code, |_z, code| ZipCode { code });

    let company = Company {
        name: "Acme Corp".into(),
        address: Address {
            city: "Metropolis".into(),
            zip: ZipCode {
                code: Tracked(10001),
            },
        },
    };

    // Law L-03: *l1.then(l2).view(&s) == *l2.view(l1.view(&s))
    let company_address_lens = company_lens.clone().then(address_zip_lens.clone());
    assert_eq!(
        *company_address_lens.view(&company),
        *address_zip_lens.view(company_lens.view(&company))
    );

    // 3-level view chaining (Contract C-04)
    let company_code_lens = company_lens
        .clone()
        .then(address_zip_lens.clone())
        .then(zip_code_lens.clone());
    assert_eq!(*company_code_lens.view(&company), Tracked(10001));

    // Contract C-06: 3-level set same value performs 0 clones
    let c = company.clone();
    CLONES.with(|cnt| cnt.set(0));
    let same = company_code_lens.set(c, Tracked(10001));
    assert_eq!(
        CLONES.with(|cnt| cnt.get()),
        0,
        "3-level set on unchanged value must perform 0 clones"
    );
    assert_eq!(*company_code_lens.view(&same), Tracked(10001));

    // Contract C-07: forget_view interop with NoView lens
    let noview_company_lens = company_lens.forget_view();
    let legacy_zip_lens = Lens::new(|a: &Address| a.zip.clone(), |a, zip| Address { zip, ..a });
    let interop_lens = noview_company_lens.then(legacy_zip_lens);
    assert_eq!(interop_lens.get(&company).code, Tracked(10001));
}

#[test]
fn test_borrowed_focus_type_composition_via_forget_view() {
    #[derive(Clone, PartialEq, Debug)]
    struct Pair<'a> {
        y: u32,
        _marker: core::marker::PhantomData<&'a ()>,
    }
    #[derive(Clone, PartialEq, Debug)]
    struct W<'a> {
        p: Pair<'a>,
    }

    let w_p_lens = Lens::from_view(|w: &W| &w.p, |_w, p| W { p });
    let p_y_lens = Lens::from_view(
        |p: &Pair| &p.y,
        |_p, y| Pair {
            y,
            _marker: core::marker::PhantomData,
        },
    );

    let w = W {
        p: Pair {
            y: 42,
            _marker: core::marker::PhantomData,
        },
    };

    assert_eq!(w_p_lens.view(&w).y, 42);

    let composed = w_p_lens.forget_view().then(p_y_lens);
    assert_eq!(composed.get(&w), 42);
    let updated = composed.set(w, 99);
    assert_eq!(updated.p.y, 99);
}
