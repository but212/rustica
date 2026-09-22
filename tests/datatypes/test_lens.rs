use quickcheck_macros::quickcheck;
use rustica::datatypes::lens::Lens;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

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

// Contract C-02: Single getter execution in modify
#[test]
fn test_modify_calls_getter_exactly_once() {
    static GET_COUNT: AtomicUsize = AtomicUsize::new(0);

    let lens = Lens::new(
        |p: &TestPerson| {
            GET_COUNT.fetch_add(1, Ordering::SeqCst);
            p.name.clone()
        },
        |p, name| TestPerson { name, ..p },
    );

    let person = TestPerson {
        name: "Alice".into(),
        age: 30,
    };

    let _ = lens.modify(person, |name| format!("Dr. {}", name));
    assert_eq!(GET_COUNT.load(Ordering::SeqCst), 1);
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
    struct Address {
        city: String,
    }
    #[derive(Clone, Debug, PartialEq)]
    struct Company {
        address: Address,
    }

    let company_address_lens = Lens::new(
        |c: &Company| c.address.clone(),
        |_c, address| Company { address },
    );
    let address_city_lens = Lens::new(|a: &Address| a.city.clone(), |_a, city| Address { city });

    let company_city_lens = company_address_lens.then(address_city_lens);

    let company = Company {
        address: Address {
            city: "Metropolis".into(),
        },
    };

    assert_eq!(company_city_lens.get(&company), "Metropolis");
    let moved = company_city_lens.set(company, "Gotham".into());
    assert_eq!(moved.address.city, "Gotham");
}
