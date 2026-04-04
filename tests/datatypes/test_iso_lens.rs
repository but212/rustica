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
fn test_iso_lens_core_behavior_and_laws() {
    let lens = IsoLens::new(NameIso);
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };

    // 1. Core API: get, set, set_focus
    let (focus, ctx) = lens.get(&person);
    assert_eq!(focus, "Alice");
    assert_eq!(ctx, person);

    let updated = lens.set(&("Bob".to_string(), person.clone()));
    assert_eq!(updated.name, "Bob");
    assert_eq!(
        lens.set_focus(&person, &"Charlie".to_string()).name,
        "Charlie"
    );

    // 2. Lens Laws (Get-Set, Set-Get, Set-Set)
    // Law 1: set(get(s)) == s
    assert_eq!(lens.set(&lens.get(&person)), person);
    assert_eq!(lens.set_focus(&person, &lens.get(&person).0), person);

    // Law 2: get(set(s, v)) == v
    let new_name = "David".to_string();
    assert_eq!(lens.get(&lens.set_focus(&person, &new_name)).0, new_name);

    // Law 3: set(set(s, v1), v2) == set(s, v2)
    let s_twice = lens.set_focus(
        &lens.set_focus(&person, &"V1".to_string()),
        &"V2".to_string(),
    );
    assert_eq!(s_twice, lens.set_focus(&person, &"V2".to_string()));

    // 3. Transformation: modify & modify_focus
    assert_eq!(
        lens.modify_focus(&person, |n| n.to_uppercase()).name,
        "ALICE"
    );
    assert_eq!(lens.iso_ref().forward(&person).0, "Alice");
}

#[test]
fn test_iso_lens_composition() {
    let outer = Outer {
        inner: Inner { value: 42 },
    };
    let composed = IsoLens::new(InnerIso).compose(IsoLens::new(ValuePairIso));

    // Verify round-trip through composition
    let got = composed.get(&outer);
    assert_eq!(got.0, 42);

    let updated = composed.set(&(
        100,
        Outer {
            inner: Inner { value: 100 },
        },
    ));
    assert_eq!(updated.inner.value, 100);
}
