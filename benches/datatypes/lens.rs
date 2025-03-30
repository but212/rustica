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

    // Create lenses
    let name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    );

    let age_lens = Lens::new(
        |p: &Person| p.age,
        |p: Person, age: u32| Person { age, ..p },
    );

    let address_lens = Lens::new(
        |p: &Person| p.address.clone(),
        |p: Person, address: Address| Person { address, ..p },
    );

    let street_lens = Lens::new(
        |a: &Address| a.street.clone(),
        |a: Address, street: String| Address { street, ..a },
    );

    let tags_lens = Lens::new(
        |p: &Person| p.tags.clone(),
        |p: Person, tags: Vec<String>| Person { tags, ..p },
    );

    let metadata_lens = Lens::new(
        |p: &Person| p.metadata.clone(),
        |p: Person, metadata: HashMap<String, String>| Person { metadata, ..p },
    );

    let team_members_lens = Lens::new(
        |t: &Team| t.members.clone(),
        |t: Team, members: Vec<Person>| Team { members, ..t },
    );

    let age_string_lens = age_lens
        .clone()
        .fmap(|n: u32| n.to_string(), |s: String| s.parse().unwrap_or(0));

    // Basic operations
    group.bench_function("get_simple", |b| {
        b.iter(|| black_box(name_lens.get(&person)));
    });

    group.bench_function("set_simple", |b| {
        b.iter(|| black_box(name_lens.set(person.clone(), "Jane".to_string())));
    });

    group.bench_function("modify_simple", |b| {
        b.iter(|| black_box(name_lens.modify(person.clone(), |name| name.to_uppercase())));
    });

    // Nested operations
    group.bench_function("get_nested", |b| {
        b.iter(|| {
            let addr = address_lens.get(&person);
            black_box(street_lens.get(&addr));
        });
    });

    group.bench_function("set_nested", |b| {
        b.iter(|| {
            black_box(address_lens.modify(person.clone(), |addr| {
                street_lens.set(addr, "789 New Road".to_string())
            }));
        });
    });

    // Collection operations
    group.bench_function("modify_collection", |b| {
        b.iter(|| {
            black_box(tags_lens.modify(person.clone(), |mut tags| {
                tags.push("functional-programming".to_string());
                tags
            }));
        });
    });

    group.bench_function("modify_hashmap", |b| {
        b.iter(|| {
            black_box(metadata_lens.modify(person.clone(), |mut map| {
                map.insert("last_updated".to_string(), "2023-05-15".to_string());
                map
            }));
        });
    });

    // Lens composition
    group.bench_function("manual_composition", |b| {
        b.iter(|| {
            let members = team_members_lens.get(&team);
            if !members.is_empty() {
                let address = address_lens.get(&members[0]);
                black_box(street_lens.get(&address));
            }
        });
    });

    // Lens transformation
    group.bench_function("fmap_get", |b| {
        b.iter(|| black_box(age_string_lens.get(&person)));
    });

    group.bench_function("fmap_set", |b| {
        b.iter(|| black_box(age_string_lens.set(person.clone(), "50".to_string())));
    });

    // Use cases
    group.bench_function("use_case_bulk_processing", |b| {
        b.iter(|| {
            black_box(team_members_lens.modify(team.clone(), |members| {
                members
                    .into_iter()
                    .map(|p| {
                        let p = age_lens.modify(p, |age| age + 1);
                        tags_lens.modify(p, |mut tags| {
                            tags.push("updated".to_string());
                            tags
                        })
                    })
                    .collect()
            }));
        });
    });

    group.finish();
}
