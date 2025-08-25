use rustica::datatypes::iso_lens::IsoLens;
use rustica::traits::iso::Iso;

// --- Test Data Structures ---

#[derive(Clone, Debug, PartialEq)]
struct Address {
    street: String,
    city: String,
}

#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: u32,
    address: Address,
}

#[derive(Clone, Debug, PartialEq)]
struct Inner {
    value: i32,
}

#[derive(Clone, Debug, PartialEq)]
struct Outer {
    inner: Inner,
}

// --- Helper Iso Implementations ---

// Focuses Person.name using the (FocusType, S) pattern
struct NameIso;
impl Iso<Person, (String, Person)> for NameIso {
    type From = Person;
    type To = (String, Person);

    fn forward(&self, from: &Person) -> (String, Person) {
        (from.name.clone(), from.clone())
    }

    fn backward(&self, to: &(String, Person)) -> Person {
        let (new_name, original) = to;
        Person {
            name: new_name.clone(),
            ..original.clone()
        }
    }
}

// For composition example: Iso between Outer and Inner (true isomorphism since Outer has only Inner)
struct InnerIso;
impl Iso<Outer, Inner> for InnerIso {
    type From = Outer;
    type To = Inner;

    fn forward(&self, from: &Outer) -> Inner {
        from.inner.clone()
    }

    fn backward(&self, to: &Inner) -> Outer {
        Outer { inner: to.clone() }
    }
}

// For composition example: Iso from Inner to (i32, Outer)
// This follows the docs pattern where the target includes the original S context (Outer).
struct ValuePairIso;
impl Iso<Inner, (i32, Outer)> for ValuePairIso {
    type From = Inner;
    type To = (i32, Outer);

    fn forward(&self, from: &Inner) -> (i32, Outer) {
        (
            from.value,
            Outer {
                inner: from.clone(),
            },
        )
    }

    fn backward(&self, to: &(i32, Outer)) -> Inner {
        Inner { value: to.0 }
    }
}

// --- Test Cases ---

#[test]
fn test_iso_lens_new_get_set_modify() {
    let lens = IsoLens::new(NameIso);
    let p = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    // get returns (focus, context)
    let got = lens.get(&p);
    assert_eq!(got.0, "Alice".to_string());
    assert_eq!(got.1, p.clone());

    // set with a tuple (new focus, context)
    let updated = lens.set(&("Bob".to_string(), p.clone()));
    assert_eq!(updated.name, "Bob");
    assert_eq!(updated.age, 30);
    assert_eq!(updated.address.street, "123 Main St");

    // modify: change the focus via A -> A
    let modified = lens.modify(&p, |(n, s)| (n.to_uppercase(), s));
    assert_eq!(modified.name, "ALICE");
    assert_eq!(modified.age, 30);
}

#[test]
fn test_iso_lens_set_focus_and_modify_focus() {
    let lens = IsoLens::new(NameIso);
    let p = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    // set_focus
    let updated = lens.set_focus(&p, &"Bob".to_string());
    assert_eq!(updated.name, "Bob");
    assert_eq!(updated.age, 30);

    // modify_focus
    let modified = lens.modify_focus(&p, |name| format!("{name}!"));
    assert_eq!(modified.name, "Alice!");
    assert_eq!(modified.address.street, "123 Main St");
}

#[test]
fn test_iso_lens_laws_using_set() {
    let lens = IsoLens::new(NameIso);
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    // 1. Get-Set: set(get(s)) == s
    let a_from_s = lens.get(&person);
    assert_eq!(lens.set(&a_from_s), person);

    // 2. Set-Get: get(set(s, v)).0 == v.0 (compare focus)
    let new_name = "Bob".to_string();
    let updated = lens.set(&(new_name.clone(), person.clone()));
    let got_after = lens.get(&updated);
    assert_eq!(got_after.0, new_name);

    // 3. Set-Set: set(set(s, v1), v2) == set(s, v2)
    let v1 = ("Charlie".to_string(), person.clone());
    let v2 = ("David".to_string(), person.clone());
    let s1 = lens.set(&v1);
    let set_twice = lens.set(&(v2.0.clone(), s1.clone()));
    let set_direct = lens.set(&v2);
    assert_eq!(set_twice, set_direct);
}

#[test]
fn test_iso_lens_laws_using_set_focus_and_modify_focus() {
    let lens = IsoLens::new(NameIso);
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    // 1. Get-Set (set_focus variant): set_focus(s, get(s).0) == s
    let focus_val = lens.get(&person).0;
    assert_eq!(lens.set_focus(&person, &focus_val), person);

    // 2. Set-Get (set_focus variant): get(set_focus(s, v)).0 == v
    let name2 = "Bob".to_string();
    let s2 = lens.set_focus(&person, &name2);
    assert_eq!(lens.get(&s2).0, name2);

    // 3. Set-Set (set_focus variant)
    let n1 = "Charlie".to_string();
    let n2 = "David".to_string();
    let s_prime = lens.set_focus(&person, &n1);
    assert_eq!(lens.set_focus(&s_prime, &n2), lens.set_focus(&person, &n2));

    // modify_focus identity law
    let s_mod_id = lens.modify_focus(&person, |n| n);
    assert_eq!(s_mod_id, person);

    // get(modify_focus(s, f)).0 == f(get(s).0)
    let s_mod = lens.modify_focus(&person, |n| n.to_uppercase());
    assert_eq!(lens.get(&s_mod).0, person.name.to_uppercase());
}

#[test]
fn test_iso_lens_iso_ref() {
    let lens = IsoLens::new(NameIso);
    let p = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    let iso = lens.iso_ref();
    let (name, _ctx) = iso.forward(&p);
    assert_eq!(name, "Alice".to_string());
}

#[test]
fn test_iso_lens_composition() {
    let outer = Outer {
        inner: Inner { value: 42 },
    };

    let outer_lens = IsoLens::new(InnerIso);
    let value_pair_lens = IsoLens::new(ValuePairIso);

    let composed = outer_lens.compose(value_pair_lens);

    // Get path
    let got = composed.get(&outer);
    assert_eq!(got.0, 42);

    // Set path
    let updated = composed.set(&(
        100,
        Outer {
            inner: Inner { value: 100 },
        },
    ));
    assert_eq!(updated.inner.value, 100);
}
