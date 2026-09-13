use crate::harness::Harness;
use rustica::datatypes::lens::Lens;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: u32,
}

pub fn lens_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Lens");
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    let name_lens = Lens::new(
        |person: &Person| person.name.clone(),
        |person: Person, name: String| Person { name, ..person },
    );

    // Compare the structural-sharing fast path with the explicit always-update path.
    group.bench_fn("set_same_value", || {
        black_box(name_lens.set(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_always_same_value", || {
        black_box(name_lens.set_always(black_box(person.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_different_value", || {
        black_box(name_lens.set(black_box(person.clone()), "Bob".to_string()));
    });

    group.bench_fn("modify_changed_value", || {
        black_box(name_lens.modify(black_box(person.clone()), |name| name + "!"));
    });
}
