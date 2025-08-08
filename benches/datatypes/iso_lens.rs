use criterion::Criterion;
use rustica::datatypes::iso_lens::IsoLens;
use rustica::traits::iso::Iso;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: u32,
    email: String,
}

#[derive(Clone, Debug, PartialEq)]
struct Address {
    street: String,
    city: String,
    zip: String,
}

#[derive(Clone, Debug, PartialEq)]
struct Employee {
    person: Person,
    address: Address,
    salary: u64,
}

// Simple Iso for Person name field
struct NameIso;
impl Iso<Person, (String, Person)> for NameIso {
    type From = Person;
    type To = (String, Person);

    fn forward(&self, from: &Person) -> (String, Person) {
        (from.name.clone(), from.clone())
    }

    fn backward(&self, to: &(String, Person)) -> Person {
        let mut p = to.1.clone();
        p.name = to.0.clone();
        p
    }
}

// Iso for Person age field
struct AgeIso;
impl Iso<Person, (u32, Person)> for AgeIso {
    type From = Person;
    type To = (u32, Person);

    fn forward(&self, from: &Person) -> (u32, Person) {
        (from.age, from.clone())
    }

    fn backward(&self, to: &(u32, Person)) -> Person {
        let mut p = to.1.clone();
        p.age = to.0;
        p
    }
}

// Iso for Employee person field
struct PersonIso;
impl Iso<Employee, (Person, Employee)> for PersonIso {
    type From = Employee;
    type To = (Person, Employee);

    fn forward(&self, from: &Employee) -> (Person, Employee) {
        (from.person.clone(), from.clone())
    }

    fn backward(&self, to: &(Person, Employee)) -> Employee {
        let mut e = to.1.clone();
        e.person = to.0.clone();
        e
    }
}

// Iso for Address city field
struct CityIso;
impl Iso<Address, (String, Address)> for CityIso {
    type From = Address;
    type To = (String, Address);

    fn forward(&self, from: &Address) -> (String, Address) {
        (from.city.clone(), from.clone())
    }

    fn backward(&self, to: &(String, Address)) -> Address {
        let mut a = to.1.clone();
        a.city = to.0.clone();
        a
    }
}

pub fn iso_lens_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IsoLens");

    // Setup test data
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        email: "alice@example.com".to_string(),
    };

    let address = Address {
        street: "123 Main St".to_string(),
        city: "New York".to_string(),
        zip: "10001".to_string(),
    };

    let employee = Employee {
        person: person.clone(),
        address: address.clone(),
        salary: 75000,
    };

    // Create lenses
    let name_lens = IsoLens::new(NameIso);
    let age_lens = IsoLens::new(AgeIso);
    let person_lens = IsoLens::new(PersonIso);
    let city_lens = IsoLens::new(CityIso);

    // Creation benchmarks
    group.bench_function("iso_lens_new", |b| {
        b.iter(|| {
            let lens = IsoLens::new(NameIso);
            black_box(lens)
        })
    });

    // Get benchmarks
    group.bench_function("iso_lens_get_simple", |b| {
        b.iter(|| {
            let result = name_lens.get(&black_box(person.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_lens_get_primitive", |b| {
        b.iter(|| {
            let result = age_lens.get(&black_box(person.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_lens_get_complex", |b| {
        b.iter(|| {
            let result = person_lens.get(&black_box(employee.clone()));
            black_box(result)
        })
    });

    // Set benchmarks
    group.bench_function("iso_lens_set_simple", |b| {
        b.iter(|| {
            let new_data = ("Bob".to_string(), black_box(person.clone()));
            let result = name_lens.set(&new_data);
            black_box(result)
        })
    });

    group.bench_function("iso_lens_set_primitive", |b| {
        b.iter(|| {
            let new_data = (35u32, black_box(person.clone()));
            let result = age_lens.set(&new_data);
            black_box(result)
        })
    });

    group.bench_function("iso_lens_set_complex", |b| {
        b.iter(|| {
            let new_person = Person {
                name: "Charlie".to_string(),
                age: 25,
                email: "charlie@example.com".to_string(),
            };
            let new_data = (new_person, black_box(employee.clone()));
            let result = person_lens.set(&new_data);
            black_box(result)
        })
    });

    // Set focus benchmarks (convenience method)
    group.bench_function("iso_lens_set_focus", |b| {
        b.iter(|| {
            let result = name_lens.set_focus(&black_box(person.clone()), &"David".to_string());
            black_box(result)
        })
    });

    group.bench_function("iso_lens_set_focus_primitive", |b| {
        b.iter(|| {
            let result = age_lens.set_focus(&black_box(person.clone()), &40u32);
            black_box(result)
        })
    });

    // Modify benchmarks
    group.bench_function("iso_lens_modify", |b| {
        b.iter(|| {
            let result = name_lens.modify(&black_box(person.clone()), |(name, p)| {
                (format!("Mr. {}", name), p)
            });
            black_box(result)
        })
    });

    group.bench_function("iso_lens_modify_focus", |b| {
        b.iter(|| {
            let result =
                name_lens.modify_focus(&black_box(person.clone()), |name| name.to_uppercase());
            black_box(result)
        })
    });

    group.bench_function("iso_lens_modify_primitive", |b| {
        b.iter(|| {
            let result = age_lens.modify_focus(&black_box(person.clone()), |age| age + 1);
            black_box(result)
        })
    });

    // Lens laws verification benchmarks
    group.bench_function("iso_lens_get_set_law", |b| {
        b.iter(|| {
            let original = black_box(person.clone());
            let got = name_lens.get(&original);
            let restored = name_lens.set(&got);
            black_box(restored)
        })
    });

    group.bench_function("iso_lens_set_get_law", |b| {
        b.iter(|| {
            let original = black_box(person.clone());
            let new_name = "Test".to_string();
            let updated = name_lens.set_focus(&original, &new_name);
            let retrieved = name_lens.get(&updated);
            black_box(retrieved)
        })
    });

    // Iso reference benchmark
    group.bench_function("iso_lens_iso_ref", |b| {
        b.iter(|| {
            let iso_ref = name_lens.iso_ref();
            let result = iso_ref.forward(&black_box(person.clone()));
            black_box(result)
        })
    });

    // Chained operations benchmarks
    group.bench_function("iso_lens_chained_operations", |b| {
        b.iter(|| {
            let mut result = black_box(person.clone());
            result = name_lens.set_focus(&result, &"Eve".to_string());
            result = age_lens.set_focus(&result, &28u32);
            black_box(result)
        })
    });

    // Complex modification benchmarks
    group.bench_function("iso_lens_complex_modify", |b| {
        b.iter(|| {
            let result = person_lens.modify_focus(&black_box(employee.clone()), |mut p| {
                p.name = p.name.to_uppercase();
                p.age += 1;
                p
            });
            black_box(result)
        })
    });

    // Performance comparison: direct field access vs lens
    group.bench_function("direct_field_access", |b| {
        b.iter(|| {
            let mut result = black_box(person.clone());
            result.name = "Direct".to_string();
            result.age = 99;
            black_box(result)
        })
    });

    group.bench_function("lens_field_access", |b| {
        b.iter(|| {
            let mut result = black_box(person.clone());
            result = name_lens.set_focus(&result, &"Lens".to_string());
            result = age_lens.set_focus(&result, &99u32);
            black_box(result)
        })
    });

    // Large structure benchmarks
    group.bench_function("iso_lens_large_structure", |b| {
        let large_employee = Employee {
            person: Person {
                name: "Large".repeat(100),
                age: 30,
                email: "large@example.com".repeat(10),
            },
            address: Address {
                street: "Street".repeat(50),
                city: "City".repeat(20),
                zip: "12345".to_string(),
            },
            salary: 100000,
        };

        b.iter(|| {
            let result = person_lens.modify_focus(&black_box(large_employee.clone()), |mut p| {
                p.age += 1;
                p
            });
            black_box(result)
        })
    });

    // Benchmarks for CityIso usage
    group.bench_function("iso_lens_city_get", |b| {
        b.iter(|| {
            let addr = black_box(address.clone());
            let city_data = city_lens.get(&addr);
            black_box(city_data)
        })
    });

    group.bench_function("iso_lens_city_set", |b| {
        b.iter(|| {
            let addr = black_box(address.clone());
            let new_city_data = ("Updated City".to_string(), addr.clone());
            let updated = city_lens.set(&new_city_data);
            black_box(updated)
        })
    });

    group.bench_function("iso_lens_city_modify", |b| {
        b.iter(|| {
            let addr = black_box(address.clone());
            let updated = city_lens.modify(&addr, |(city, mut addr)| {
                addr.city = format!("{} - Modified", city);
                (city, addr)
            });
            black_box(updated)
        })
    });

    group.finish();
}
