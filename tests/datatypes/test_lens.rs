use std::cell::Cell;
use std::rc::Rc;

use quickcheck_macros::quickcheck;
use rustica::datatypes::lens::Lens;

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestPerson {
    name: String,
    age: u32,
}

fn name_lens() -> Lens<
    TestPerson,
    String,
    impl Fn(&TestPerson) -> &String + Clone,
    impl Fn(TestPerson, String) -> TestPerson + Clone,
> {
    Lens::new(|p: &TestPerson| &p.name, |p, name| TestPerson { name, ..p })
}

fn age_lens() -> Lens<
    TestPerson,
    u32,
    impl Fn(&TestPerson) -> &u32 + Clone,
    impl Fn(TestPerson, u32) -> TestPerson + Clone,
> {
    Lens::new(|p: &TestPerson| &p.age, |p, age| TestPerson { age, ..p })
}

// Law 1: GetSet Law (l.set(s.clone(), l.to_value(&s)) == s)
#[test]
fn test_lens_get_set_law() {
    let lens = name_lens();
    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };
    assert_eq!(lens.set(person.clone(), lens.to_value(&person)), person);
}

// Law 2: SetGet Law (*l.view(&l.set(s, v)) == v)
#[quickcheck]
fn test_lens_set_get_law(age: u32) -> bool {
    let lens = age_lens();
    let person = TestPerson {
        name: "Bob".into(),
        age: 20,
    };
    *lens.view(&lens.set(person, age)) == age
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

// Contract C-02: C-CONV accessors view(&S) -> &A and to_value(&S) -> A
#[test]
fn test_lens_c_conv_accessors() {
    let lens = name_lens();
    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };

    // Free borrowed view (0 B)
    assert_eq!(lens.view(&person), "Alice");

    // Explicit owned extraction
    assert_eq!(lens.to_value(&person), "Alice");
}

// Contract C-01: Lens works on non-Clone structs and fields
#[test]
fn test_lens_non_clone_struct() {
    struct NonClonePerson {
        id: u64,
    }

    let id_lens = Lens::new(|p: &NonClonePerson| &p.id, |_p, id| NonClonePerson { id });

    let p = NonClonePerson { id: 42 };
    assert_eq!(*id_lens.view(&p), 42);
    assert_eq!(id_lens.to_value(&p), 42);

    let updated = id_lens.set_always(p, 99);
    assert_eq!(*id_lens.view(&updated), 99);

    let modified = id_lens.modify_always(updated, |id| id + 1);
    assert_eq!(*id_lens.view(&modified), 100);
}

#[test]
fn test_modify_supports_non_clone_partial_eq_focus() {
    #[derive(Clone, PartialEq, Debug)]
    struct Focus(u8);

    let lens = Lens::new(
        |source: &Focus| source,
        |_source, Focus(value)| Focus(value),
    );
    assert_eq!(
        lens.modify(Focus(41), |Focus(value)| Focus(value + 1)),
        Focus(42)
    );
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
        format!("{name} Smith")
    });

    assert_eq!(updated.name, "Alice Smith");
    assert_eq!(transform_count.get(), 1);
}

// Slice 2: Contract C-03 & C-04: Zero-alloc set and single-clone modify
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
fn test_lens_set_preserves_sharing() {
    let lens = Lens::new(
        |c: &TrackedContainer| &c.item,
        |c, item| TrackedContainer { item, ..c },
    );
    let container = TrackedContainer {
        item: Tracked(42),
        id: 1,
    };

    // Contract C-03: Zero-clone set on same value
    let c = container.clone();
    CLONES.with(|cnt| cnt.set(0));
    let same = lens.set(c, Tracked(42));
    assert_eq!(
        CLONES.with(|cnt| cnt.get()),
        0,
        "set on unchanged value must perform 0 clones"
    );
    assert_eq!(same.item, Tracked(42));

    // Contract C-04: Exactly 1 clone on modify identity (0 for comparison)
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
    let rc_lens = Lens::new(
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

    let c4 = container;
    let mod_updated = lens.modify(c4, |x| Tracked(x.0 + 10));
    assert_eq!(mod_updated.item, Tracked(52));
    assert_eq!(mod_updated.id, 1, "unrelated field must be preserved");
}

// Slice 3: Contract C-10: Unified then composition across 3 levels
#[test]
fn test_lens_composed_view() {
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

    let company_lens = Lens::new(
        |c: &Company| &c.address,
        |c, address| Company { address, ..c },
    );
    let address_zip_lens = Lens::new(|a: &Address| &a.zip, |a, zip| Address { zip, ..a });
    let zip_code_lens = Lens::new(|z: &ZipCode| &z.code, |_z, code| ZipCode { code });

    let company = Company {
        name: "Acme Corp".into(),
        address: Address {
            city: "Metropolis".into(),
            zip: ZipCode {
                code: Tracked(10001),
            },
        },
    };

    // 3-level view chaining
    let company_code_lens = company_lens
        .clone()
        .then(address_zip_lens.clone())
        .then(zip_code_lens.clone());
    assert_eq!(*company_code_lens.view(&company), Tracked(10001));

    // 3-level set same value performs 0 clones
    let c = company;
    CLONES.with(|cnt| cnt.set(0));
    let same = company_code_lens.set(c, Tracked(10001));
    assert_eq!(
        CLONES.with(|cnt| cnt.get()),
        0,
        "3-level set on unchanged value must perform 0 clones"
    );
    assert_eq!(*company_code_lens.view(&same), Tracked(10001));
}

#[test]
fn test_lens_float_equality_semantics() {
    #[derive(Clone, Debug, PartialEq)]
    struct Point {
        x: f64,
        y: f64,
    }
    let lens = Lens::new(|p: &Point| &p.x, |p, x| Point { x, ..p });

    // -0.0 == 0.0 under PartialEq, so set() short-circuits and preserves original -0.0
    let s = Point { x: -0.0, y: 1.0 };
    let short_circuited = lens.set(s.clone(), 0.0);
    assert_eq!(short_circuited.x.to_bits(), (-0.0f64).to_bits());
    assert_eq!(short_circuited.y, 1.0);

    // set_always() bypasses PartialEq and assigns bit-exact 0.0
    let bit_exact = lens.set_always(s.clone(), 0.0);
    assert_eq!(bit_exact.x.to_bits(), (0.0f64).to_bits());
    assert_eq!(bit_exact.y, 1.0);

    // modify() on float behaves symmetrically
    let mod_short = lens.modify(s.clone(), |_| 0.0);
    assert_eq!(mod_short.x.to_bits(), (-0.0f64).to_bits());
    assert_eq!(mod_short.y, 1.0);

    let mod_always = lens.modify_always(s, |_| 0.0);
    assert_eq!(mod_always.x.to_bits(), (0.0f64).to_bits());
    assert_eq!(mod_always.y, 1.0);
}
