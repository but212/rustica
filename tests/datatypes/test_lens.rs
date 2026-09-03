use rustica::datatypes::lens::Lens;
use std::rc::Rc;

// --- Test Data Structures ---

#[derive(Clone, Debug, PartialEq)]
struct Point {
    x: f64,
    y: f64,
}

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

// --- Helper Lenses ---

type PointXLens = Lens<Point, f64, Box<dyn Fn(&Point) -> f64>, Box<dyn Fn(Point, f64) -> Point>>;

fn x_lens() -> PointXLens {
    Lens::new(
        Box::new(|p: &Point| p.x),
        Box::new(|p: Point, x: f64| Point { x, ..p }),
    )
}

type PersonAddressRcLens = Lens<
    Person,
    Rc<Address>,
    Box<dyn Fn(&Person) -> Rc<Address>>,
    Box<dyn Fn(Person, Rc<Address>) -> Person>,
>;

fn address_rc_lens() -> PersonAddressRcLens {
    Lens::new(
        Box::new(|p: &Person| p.address.clone()),
        Box::new(|p: Person, address: Rc<Address>| Person { address, ..p }),
    )
}

type AddressStreetLens =
    Lens<Address, String, Box<dyn Fn(&Address) -> String>, Box<dyn Fn(Address, String) -> Address>>;

fn street_lens() -> AddressStreetLens {
    Lens::new(
        Box::new(|a: &Address| a.street.clone()),
        Box::new(|a: Address, street: String| Address { street, ..a }),
    )
}

type PersonAddressValLens =
    Lens<Person, Address, Box<dyn Fn(&Person) -> Address>, Box<dyn Fn(Person, Address) -> Person>>;

fn address_val_lens() -> PersonAddressValLens {
    Lens::new(
        Box::new(|p: &Person| (*p.address).clone()),
        Box::new(|p: Person, addr: Address| Person {
            address: Rc::new(addr),
            ..p
        }),
    )
}

// --- Test Cases ---

#[test]
fn test_lens_basic_usage() {
    #[derive(Clone, Debug, PartialEq)]
    struct Person {
        name: String,
        age: u32,
    }

    let name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    );
    let age_lens = Lens::new(
        |p: &Person| p.age,
        |p: Person, age: u32| Person { age, ..p },
    );
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };

    assert_eq!(name_lens.get(&person), "Alice");
    assert_eq!(age_lens.get(&person), 30);

    let renamed = name_lens.set(person.clone(), "Bob".to_string());
    assert_eq!(
        renamed,
        Person {
            name: "Bob".to_string(),
            age: 30
        }
    );

    let older = age_lens.modify(person, |age| age + 1);
    assert_eq!(older.age, 31);
}

#[test]
fn test_lens_nested_modify_and_structural_sharing() {
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let address_lens = address_val_lens();
    let street_lens = street_lens();

    let updated = address_lens.modify(person.clone(), |address| {
        street_lens.set(address, "456 Oak Ave".to_string())
    });
    assert_eq!(updated.address.street, "456 Oak Ave");
    assert_eq!(updated.address.city, "Springfield");

    let unchanged = address_lens.modify(person.clone(), |address| {
        street_lens.set(address, "123 Main St".to_string())
    });
    assert!(Rc::ptr_eq(&person.address, &unchanged.address));
}

#[test]
fn test_lens_laws_and_structural_sharing() {
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let lens = address_rc_lens();

    // 1. GetSet Law: set(s, get(s)) == s (Also verifies structural sharing)
    let focus = lens.get(&person);
    let result = lens.set(person.clone(), focus);
    assert_eq!(result, person);
    assert!(Rc::ptr_eq(&result.address, &person.address));

    // 2. SetGet Law: get(set(s, v)) == v
    let new_addr = Rc::new(Address {
        street: "456 Oak Ave".to_string(),
        city: "Shelbyville".to_string(),
    });
    let updated = lens.set(person.clone(), new_addr.clone());
    assert_eq!(lens.get(&updated), new_addr);

    // 3. SetSet Law: set(set(s, v1), v2) == set(s, v2)
    let v1 = Rc::new(Address {
        street: "V1".to_string(),
        city: "C1".to_string(),
    });
    let v2 = Rc::new(Address {
        street: "V2".to_string(),
        city: "C2".to_string(),
    });
    assert_eq!(
        lens.set(lens.set(person.clone(), v1), v2.clone()),
        lens.set(person.clone(), v2)
    );

    // 4. Identity Modification sharing
    let modified = lens.modify(person.clone(), |a| a);
    assert!(Rc::ptr_eq(&modified.address, &person.address));
}

#[test]
fn test_lens_composition_and_chaining() {
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };

    // Composing lenses: Person -> Address (val) -> Street (String)
    let composed = address_val_lens().compose(street_lens());

    // 1. Get through composition
    assert_eq!(composed.get(&person), "123 Main St");

    // 2. Set through composition (Deep update)
    let updated = composed.set(person.clone(), "456 Oak Ave".to_string());
    assert_eq!(updated.address.street, "456 Oak Ave");
    assert_ne!(Rc::as_ptr(&updated.address), Rc::as_ptr(&person.address));

    // 3. Structural sharing preserved in composition (No change)
    let unchanged = composed.set(person.clone(), "123 Main St".to_string());
    assert!(Rc::ptr_eq(&unchanged.address, &person.address));

    // 4. Chaining with 'then'
    let chained = address_val_lens().then(street_lens());
    assert_eq!(chained.get(&person), "123 Main St");
}

#[test]
fn test_lens_unconditional_updates() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();

    // set_always & modify_always bypass structural sharing evaluation
    let updated = lens.set_always(point.clone(), 10.0);
    assert_eq!(updated.x, 10.0);

    let modified = lens.modify_always(point, |x| x);
    assert_eq!(modified.x, 10.0);
}

#[test]
fn test_lens_fmap() {
    let point = Point { x: 10.0, y: 20.0 };
    let string_lens = x_lens().fmap(|x| x.to_string(), |s| s.parse::<f64>().unwrap_or(0.0));

    assert_eq!(string_lens.get(&point), "10");
    assert_eq!(string_lens.set(point, "25.5".to_string()).x, 25.5);
}
