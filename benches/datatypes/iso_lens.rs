use criterion::Criterion;
use rustica::datatypes::iso_lens::IsoLens;
use rustica::traits::iso::Iso;
use std::hint::black_box;

#[derive(Debug, PartialEq, Eq, Clone)]
struct Address {
    street: String,
    city: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Person {
    name: String,
    address: Address,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Team {
    name: String,
    members: Vec<Person>,
}

struct AddressIso;
impl Iso<Person, (Address, Person)> for AddressIso {
    type From = Person;
    type To = (Address, Person);
    fn forward(&self, from: &Person) -> (Address, Person) {
        (from.address.clone(), from.clone())
    }
    fn backward(&self, to: &(Address, Person)) -> Person {
        let mut p = to.1.clone();
        p.address = to.0.clone();
        p
    }
}

struct MembersIso;
impl Iso<Team, (Vec<Person>, Team)> for MembersIso {
    type From = Team;
    type To = (Vec<Person>, Team);
    fn forward(&self, from: &Team) -> (Vec<Person>, Team) {
        (from.members.clone(), from.clone())
    }
    fn backward(&self, to: &(Vec<Person>, Team)) -> Team {
        let mut t = to.1.clone();
        t.members = to.0.clone();
        t
    }
}

pub fn iso_lens_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IsoLens");

    let person = Person {
        name: "Alice".to_string(),
        address: Address {
            street: "Main St".to_string(),
            city: "Springfield".to_string(),
        },
    };
    let person2 = Person {
        name: "Bob".to_string(),
        address: Address {
            street: "2nd Ave".to_string(),
            city: "Springfield".to_string(),
        },
    };
    let team = Team {
        name: "Alpha Team".to_string(),
        members: vec![person.clone(), person2.clone()],
    };
    let lens = IsoLens::new(AddressIso);
    let members_lens = IsoLens::new(MembersIso);

    group.bench_function("get", |b| {
        b.iter(|| {
            let addr = lens.get(black_box(&person));
            black_box(addr)
        })
    });

    group.bench_function("set", |b| {
        b.iter(|| {
            let updated = lens.set(black_box(&(
                Address {
                    street: "Oak Ave".to_string(),
                    city: "Springfield".to_string(),
                },
                person.clone(),
            )));
            black_box(updated)
        })
    });

    group.bench_function("modify", |b| {
        b.iter(|| {
            let modified = lens.modify(black_box(&person), |a| {
                (
                    Address {
                        street: a.0.street.to_uppercase(),
                        city: a.0.city.clone(),
                    },
                    a.1.clone(),
                )
            });
            black_box(modified)
        })
    });

    group.bench_function("get_nested_member_address", |b| {
        b.iter(|| {
            let (members, _) = members_lens.get(black_box(&team));
            let addr = lens.get(&members[0]);
            black_box(addr)
        })
    });

    group.bench_function("modify_all_addresses", |b| {
        b.iter(|| {
            let modified_team = members_lens.modify(black_box(&team), |(members, team)| {
                (
                    members
                        .into_iter()
                        .map(|p| {
                            lens.modify(&p, |a| {
                                (
                                    Address {
                                        street: a.0.street.to_uppercase(),
                                        city: a.0.city.clone(),
                                    },
                                    a.1.clone(),
                                )
                            })
                        })
                        .collect::<Vec<_>>(),
                    team.clone(),
                )
            });
            black_box(modified_team)
        })
    });

    group.bench_function("bulk_uppercase_names", |b| {
        b.iter(|| {
            let modified_team = members_lens.modify(black_box(&team), |(members, team)| {
                let members: Vec<Person> = members
                    .iter()
                    .map(|p| {
                        let mut p_clone = p.clone();
                        p_clone.name = p_clone.name.to_uppercase();
                        p_clone
                    })
                    .collect();
                (members, team.clone())
            });
            black_box(modified_team)
        })
    });

    group.finish();
}
