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
    address: Rc<Address>, // Use Rc for structural sharing tests
}

// --- Helper Lenses ---

// Lens for Point.x
fn x_lens() -> Lens<Point, f64, impl Fn(&Point) -> f64, impl Fn(Point, f64) -> Point> {
    Lens::new(|p: &Point| p.x, |p: Point, x: f64| Point { x, ..p })
}

// Lens for Person.name
fn name_lens() -> Lens<Person, String, impl Fn(&Person) -> String, impl Fn(Person, String) -> Person>
{
    Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    )
}

// Lens for Person.address (focuses on the Rc<Address>)
fn address_rc_lens() -> Lens<
    Person,
    Rc<Address>,
    impl Fn(&Person) -> Rc<Address>,
    impl Fn(Person, Rc<Address>) -> Person,
> {
    Lens::new(
        |p: &Person| p.address.clone(),
        |p: Person, address: Rc<Address>| Person { address, ..p },
    )
}

// Lens for Address.street
fn street_lens()
-> Lens<Address, String, impl Fn(&Address) -> String, impl Fn(Address, String) -> Address> {
    Lens::new(
        |a: &Address| a.street.clone(),
        |a: Address, street: String| Address { street, ..a },
    )
}

// Lens for Address (focuses on the Address value inside the Rc)
// Note: This involves cloning the Address for modification
fn address_val_lens()
-> Lens<Person, Address, impl Fn(&Person) -> Address, impl Fn(Person, Address) -> Person> {
    Lens::new(
        |p: &Person| (*p.address).clone(), // Clone Address on get
        |p: Person, addr: Address| Person {
            address: Rc::new(addr), // Create new Rc on set
            ..p
        },
    )
}

// --- Test Cases ---

#[test]
fn test_lens_new_and_get() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();
    assert_eq!(lens.get(&point), 10.0);

    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let lens = name_lens();
    assert_eq!(lens.get(&person), "Alice");
}

#[test]
fn test_lens_set() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();

    // Set to a different value
    let updated_point = lens.set(point.clone(), 15.0);
    assert_eq!(updated_point.x, 15.0);
    assert_eq!(updated_point.y, 20.0); // Ensure other fields are unchanged

    // Set to the same value (test structural sharing optimization)
    let not_updated_point = lens.set(point.clone(), 10.0);
    assert_eq!(not_updated_point.x, 10.0);
    assert_eq!(not_updated_point.y, 20.0);
    // Since Point doesn't use Rc, we can't easily test pointer equality here,
    // but the logic in Lens::set should return the original `point`.

    // Test with Rc for structural sharing
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let original_address_ptr = Rc::as_ptr(&person.address);
    let lens = address_rc_lens();

    // Set Rc<Address> to a different Rc
    let new_addr = Rc::new(Address {
        street: "456 Oak Ave".to_string(),
        city: "Shelbyville".to_string(),
    });
    let updated_person = lens.set(person.clone(), new_addr.clone());
    assert!(Rc::ptr_eq(&updated_person.address, &new_addr));
    assert_ne!(Rc::as_ptr(&updated_person.address), original_address_ptr);
    assert_eq!(updated_person.name, "Alice");

    // Set Rc<Address> to the *same* Rc instance
    let not_updated_person = lens.set(person.clone(), person.address.clone());
    assert!(Rc::ptr_eq(&not_updated_person.address, &person.address));
    assert_eq!(not_updated_person.name, "Alice"); // Check other fields
}

#[test]
fn test_lens_set_always() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();

    // Set to a different value
    let updated_point = lens.set_always(point.clone(), 15.0);
    assert_eq!(updated_point.x, 15.0);
    assert_eq!(updated_point.y, 20.0);

    // Set to the same value - should still create a new object conceptually
    // (though for simple types like f64, it might optimize)
    let updated_again = lens.set_always(point.clone(), 10.0);
    assert_eq!(updated_again.x, 10.0);
    assert_eq!(updated_again.y, 20.0);

    // Test with Rc - should *not* share structure even if Rcs are equal
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let lens = address_rc_lens();
    let same_addr_rc = person.address.clone();

    let updated_person = lens.set_always(person.clone(), same_addr_rc);
    // Even though the address *content* is the same, set_always uses the provided Rc,
    // so pointer equality should hold in this specific case *if* the Rc itself is the same clone.
    // The key difference from `set` is that `set` *would* compare the inner Address values if they implement PartialEq.
    // Since Rc<T> implements PartialEq if T does, `set` *would* likely return the original person here.
    // `set_always` bypasses that check.
    assert!(Rc::ptr_eq(&updated_person.address, &person.address));
}

#[test]
fn test_lens_modify() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();

    // Modify to a different value
    let modified_point = lens.modify(point.clone(), |x| x + 5.0);
    assert_eq!(modified_point.x, 15.0);
    assert_eq!(modified_point.y, 20.0);

    // Modify to the same value (test structural sharing)
    let not_modified_point = lens.modify(point.clone(), |x| x * 1.0);
    assert_eq!(not_modified_point.x, 10.0);
    assert_eq!(not_modified_point.y, 20.0);
    // Again, can't easily test pointer equality for Point itself

    // Test with Rc for structural sharing
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let original_address_ptr = Rc::as_ptr(&person.address);
    let lens = address_val_lens(); // Lens focusing on Address value

    // Modify the Address value -> creates new Address -> creates new Rc
    let modified_person = lens.modify(person.clone(), |mut addr| {
        addr.street = "456 Oak Ave".to_string();
        addr // Return the modified Address
    });
    assert_eq!(modified_person.address.street, "456 Oak Ave");
    assert_ne!(Rc::as_ptr(&modified_person.address), original_address_ptr);

    // Modify the Address value but result is the same -> should return original Person
    let not_modified_person = lens.modify(person.clone(), |addr| {
        addr // Return the original Address clone
    });
    // Because Address implements PartialEq, Lens::modify sees the value hasn't changed
    // and returns the original `person` structure.
    assert!(Rc::ptr_eq(&not_modified_person.address, &person.address));
    assert_eq!(not_modified_person.address.street, "123 Main St");
}

#[test]
fn test_lens_modify_always() {
    let point = Point { x: 10.0, y: 20.0 };
    let lens = x_lens();

    // Modify to a different value
    let modified_point = lens.modify_always(point.clone(), |x| x + 5.0);
    assert_eq!(modified_point.x, 15.0);
    assert_eq!(modified_point.y, 20.0);

    // Modify to the same value - should still create new conceptually
    let modified_again = lens.modify_always(point.clone(), |x| x * 1.0);
    assert_eq!(modified_again.x, 10.0);
    assert_eq!(modified_again.y, 20.0);

    // Test with Rc - should *not* share structure even if value is unchanged
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };
    let original_address_ptr = Rc::as_ptr(&person.address);
    let lens = address_val_lens(); // Lens focusing on Address value

    // Modify returns same value, but modify_always bypasses check
    let updated_person = lens.modify_always(person.clone(), |addr| addr); // Return same Address value
    assert_eq!(updated_person.address.street, "123 Main St");
    // Because modify_always unconditionally calls the setter, and our
    // address_val_lens setter *always* creates a new Rc, the pointers won't match.
    assert_ne!(Rc::as_ptr(&updated_person.address), original_address_ptr);
}

#[test]
fn test_lens_fmap() {
    let point = Point { x: 10.0, y: 20.0 };
    let x_lens = x_lens();

    // Map f64 to String and back
    let x_string_lens = x_lens.fmap(
        |x| x.to_string(),                   // f64 -> String
        |s| s.parse::<f64>().unwrap_or(0.0), // String -> f64
    );

    // Get the string representation
    assert_eq!(x_string_lens.get(&point), "10"); // Note: to_string might format differently

    // Set using the string representation
    let updated_point = x_string_lens.set(point.clone(), "25.5".to_string());
    assert_eq!(updated_point.x, 25.5);
    assert_eq!(updated_point.y, 20.0); // Other fields unchanged

    // Modify using the string representation
    let modified_point = x_string_lens.modify(point, |s| format!("{}0", s)); // "10" -> "100"
    assert_eq!(modified_point.x, 100.0);
    assert_eq!(modified_point.y, 20.0);
}

#[test]
fn test_lens_composition() {
    let person = Person {
        name: "Alice".to_string(),
        address: Rc::new(Address {
            street: "123 Main St".to_string(),
            city: "Springfield".to_string(),
        }),
    };

    let person_addr_lens = address_val_lens();
    let addr_street_lens = street_lens();

    // --- Test Get Composition ---
    // Get Address, then get Street from Address
    let address = person_addr_lens.get(&person);
    let street = addr_street_lens.get(&address);
    assert_eq!(street, "123 Main St");

    // --- Test Set/Modify Composition ---
    // Modify Person using address_lens, inside the modification,
    // use street_lens to set the street on the Address.

    let updated_person = person_addr_lens.modify(person.clone(), |addr| {
        addr_street_lens.set(addr, "456 Oak Ave".to_string())
    });

    assert_eq!(updated_person.name, "Alice");
    assert_eq!(updated_person.address.street, "456 Oak Ave");
    assert_eq!(updated_person.address.city, "Springfield");

    // Check pointer inequality to confirm new Address and Rc were created
    let original_address_ptr = Rc::as_ptr(&person.address);
    assert_ne!(Rc::as_ptr(&updated_person.address), original_address_ptr);

    // --- Test Composition where inner modify results in no change ---
    // Modify the street, but set it to the same value.
    // The `street_lens.set` inside should return the original Address due to PartialEq.
    // Then, `person_addr_lens.modify` should see the Address hasn't changed
    // and return the original person structure (structural sharing).
    let not_updated_person = person_addr_lens.modify(person.clone(), |addr| {
        addr_street_lens.set(addr, "123 Main St".to_string()) // Set to same value
    });
    assert!(Rc::ptr_eq(&not_updated_person.address, &person.address)); // Pointers should be equal
    assert_eq!(not_updated_person.address.street, "123 Main St");
}
