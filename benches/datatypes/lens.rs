use criterion::{black_box, Criterion};
use rustica::datatypes::lens::Lens;
use std::collections::HashMap;

// Simple test structures
#[derive(Debug, PartialEq, Eq, Clone)]
struct Address {
    street: String,
    city: String,
    zip: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Person {
    name: String,
    age: u32,
    address: Address,
    tags: Vec<String>,
    metadata: HashMap<String, String>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Team {
    name: String,
    members: Vec<Person>,
}

pub fn lens_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Lens");

    // Create test data
    let mut metadata = HashMap::new();
    metadata.insert("employee_id".to_string(), "E12345".to_string());
    metadata.insert("department".to_string(), "Engineering".to_string());

    let person = Person {
        name: "John".to_string(),
        age: 42,
        address: Address {
            street: "123 Main St".to_string(),
            city: "Metropolis".to_string(),
            zip: "12345".to_string(),
        },
        tags: vec![
            "developer".to_string(),
            "rust".to_string(),
            "senior".to_string(),
        ],
        metadata: metadata.clone(),
    };

    let team = Team {
        name: "Alpha Team".to_string(),
        members: vec![
            person.clone(),
            Person {
                name: "Jane".to_string(),
                age: 35,
                address: Address {
                    street: "456 Oak Ave".to_string(),
                    city: "Smallville".to_string(),
                    zip: "54321".to_string(),
                },
                tags: vec!["designer".to_string(), "ui/ux".to_string()],
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("employee_id".to_string(), "E67890".to_string());
                    m.insert("department".to_string(), "Design".to_string());
                    m
                },
            },
        ],
    };

    // ======== BASIC OPERATIONS ========

    // Create basic lenses
    let name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    );

    let age_lens = Lens::new(
        |p: &Person| p.age,
        |p: Person, age: u32| Person { age, ..p },
    );

    group.bench_function("get_simple", |b| {
        b.iter(|| {
            black_box(name_lens.get(&person));
        });
    });

    group.bench_function("set_simple", |b| {
        b.iter(|| {
            black_box(name_lens.set(person.clone(), "Jane".to_string()));
        });
    });

    group.bench_function("modify_simple", |b| {
        b.iter(|| {
            black_box(name_lens.modify(person.clone(), |name: String| name.to_uppercase()));
        });
    });

    // ======== NESTED STRUCTURES ========

    // Address lens
    let address_lens = Lens::new(
        |p: &Person| p.address.clone(),
        |p: Person, address: Address| Person { address, ..p },
    );

    // Nested street lens
    let street_lens = Lens::new(
        |a: &Address| a.street.clone(),
        |a: Address, street: String| Address { street, ..a },
    );

    group.bench_function("get_nested", |b| {
        b.iter(|| {
            let addr = address_lens.get(&person);
            black_box(street_lens.get(&addr));
        });
    });

    group.bench_function("set_nested", |b| {
        b.iter(|| {
            black_box(address_lens.modify(person.clone(), |addr: Address| {
                street_lens.set(addr, "789 New Road".to_string())
            }));
        });
    });

    // ======== COLLECTION OPERATIONS ========

    // Lens for the tags vector
    let tags_lens = Lens::new(
        |p: &Person| p.tags.clone(),
        |p: Person, tags: Vec<String>| Person { tags, ..p },
    );

    // Lens for metadata HashMap
    let metadata_lens = Lens::new(
        |p: &Person| p.metadata.clone(),
        |p: Person, metadata: HashMap<String, String>| Person { metadata, ..p },
    );

    group.bench_function("get_collection", |b| {
        b.iter(|| {
            black_box(tags_lens.get(&person));
        });
    });

    group.bench_function("modify_collection", |b| {
        b.iter(|| {
            black_box(tags_lens.modify(person.clone(), |tags: Vec<String>| {
                let mut new_tags = tags;
                new_tags.push("functional-programming".to_string());
                new_tags
            }));
        });
    });

    group.bench_function("get_hashmap", |b| {
        b.iter(|| {
            black_box(metadata_lens.get(&person));
        });
    });

    group.bench_function("modify_hashmap", |b| {
        b.iter(|| {
            black_box(
                metadata_lens.modify(person.clone(), |mut map: HashMap<String, String>| {
                    map.insert("last_updated".to_string(), "2023-05-15".to_string());
                    map
                }),
            );
        });
    });

    // ======== LENS COMPOSITION ========

    // Create composed lens for team -> first member -> address -> street
    let team_members_lens = Lens::new(
        |t: &Team| t.members.clone(),
        |t: Team, members: Vec<Person>| Team { members, ..t },
    );

    group.bench_function("manual_composition", |b| {
        b.iter(|| {
            // First get team members
            let members = team_members_lens.get(&team);
            // Get first member
            if !members.is_empty() {
                let first_member = &members[0];
                // Get address
                let address = address_lens.get(first_member);
                // Get street
                black_box(street_lens.get(&address));
            }
        });
    });

    // ======== LENS TRANSFORMATION (fmap) ========

    // Create a lens that views age as a string
    let age_string_lens = age_lens
        .clone()
        .fmap(|n: u32| n.to_string(), |s: String| s.parse().unwrap_or(0));

    group.bench_function("fmap_get", |b| {
        b.iter(|| {
            black_box(age_string_lens.get(&person));
        });
    });

    group.bench_function("fmap_set", |b| {
        b.iter(|| {
            black_box(age_string_lens.set(person.clone(), "50".to_string()));
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Use case 1: Data validation and transformation
    group.bench_function("use_case_validation", |b| {
        b.iter(|| {
            // Validate and normalize a person's name
            black_box(name_lens.modify(person.clone(), |name: String| {
                let name = name.trim();
                if name.is_empty() {
                    "Unknown".to_string()
                } else {
                    // Capitalize first letter of each word
                    name.split_whitespace()
                        .map(|word| {
                            let mut chars = word.chars();
                            match chars.next() {
                                None => String::new(),
                                Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(" ")
                }
            }));
        });
    });

    // Use case 2: Deep nested update
    group.bench_function("use_case_deep_update", |b| {
        b.iter(|| {
            black_box(
                team_members_lens.modify(team.clone(), |members: Vec<Person>| {
                    let mut members = members;
                    if !members.is_empty() {
                        // Update first member's address city
                        members[0] =
                            address_lens.modify(members[0].clone(), |addr: Address| Address {
                                city: "New Metropolis".to_string(),
                                ..addr
                            });
                    }
                    members
                }),
            );
        });
    });

    // Use case 3: Working with optional data
    let optional_person = Some(person.clone());
    let opt_lens = Lens::new(
        |opt: &Option<Person>| opt.clone(),
        |_: Option<Person>, new_opt: Option<Person>| new_opt,
    );

    group.bench_function("use_case_optional_data", |b| {
        b.iter(|| {
            black_box(
                opt_lens.modify(optional_person.clone(), |opt: Option<Person>| {
                    opt.map(|p| name_lens.modify(p, |name: String| format!("Dr. {}", name)))
                }),
            );
        });
    });

    // Use case 4: Bulk data processing with lenses
    group.bench_function("use_case_bulk_processing", |b| {
        b.iter(|| {
            black_box(
                team_members_lens.modify(team.clone(), |members: Vec<Person>| {
                    members
                        .into_iter()
                        .map(|person| {
                            // Increase everyone's age by 1
                            let person = age_lens.modify(person, |age: u32| age + 1);

                            // Add a tag to everyone
                            tags_lens.modify(person, |tags: Vec<String>| {
                                let mut tags = tags;
                                tags.push("updated".to_string());
                                tags
                            })
                        })
                        .collect()
                }),
            );
        });
    });

    group.finish();
}
