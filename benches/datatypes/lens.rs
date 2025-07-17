use criterion::Criterion;
use rustica::datatypes::lens::Lens;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
struct Person {
    name: String,
    age: u32,
    email: String,
}

#[derive(Clone)]
struct LargeStruct {
    data: Vec<i32>,
    metadata: String,
    counter: u64,
}

pub fn lens_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Lens");

    // Setup test data
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        email: "alice@example.com".to_string(),
    };

    let large_struct = LargeStruct {
        data: (0..1000).collect(),
        metadata: "Large dataset for benchmarking".to_string(),
        counter: 42,
    };

    // Lens for metadata field
    let metadata_lens = Lens::new(
        |s: &LargeStruct| s.metadata.clone(),
        |s: LargeStruct, new_metadata: String| LargeStruct {
            data: s.data,
            metadata: new_metadata,
            counter: s.counter,
        },
    );

    // Create lenses
    let name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| Person { name, ..p },
    );

    let age_lens = Lens::new(
        |p: &Person| p.age,
        |p: Person, age: u32| Person { age, ..p },
    );

    let counter_lens = Lens::new(
        |s: &LargeStruct| s.counter,
        |s: LargeStruct, counter: u64| LargeStruct { counter, ..s },
    );

    let data_lens = Lens::new(
        |s: &LargeStruct| s.data.clone(),
        |s: LargeStruct, data: Vec<i32>| LargeStruct { data, ..s },
    );

    // Creation benchmarks
    group.bench_function("lens_new", |b| {
        b.iter(|| {
            let lens = Lens::new(
                |p: &Person| p.name.clone(),
                |p: Person, name: String| Person { name, ..p },
            );
            black_box(lens)
        })
    });

    // Get benchmarks
    group.bench_function("lens_get_simple", |b| {
        b.iter(|| {
            let result = name_lens.get(&black_box(person.clone()));
            black_box(result)
        })
    });

    group.bench_function("lens_get_primitive", |b| {
        b.iter(|| {
            let result = age_lens.get(&black_box(person.clone()));
            black_box(result)
        })
    });

    group.bench_function("lens_get_large_data", |b| {
        b.iter(|| {
            let result = data_lens.get(&black_box(large_struct.clone()));
            black_box(result)
        })
    });

    // Set benchmarks
    group.bench_function("lens_set_same_value", |b| {
        b.iter(|| {
            let result = name_lens.set(black_box(person.clone()), "Alice".to_string());
            black_box(result)
        })
    });

    group.bench_function("lens_set_different_value", |b| {
        b.iter(|| {
            let result = name_lens.set(black_box(person.clone()), "Bob".to_string());
            black_box(result)
        })
    });

    group.bench_function("lens_set_primitive", |b| {
        b.iter(|| {
            let result = age_lens.set(black_box(person.clone()), 35);
            black_box(result)
        })
    });

    group.bench_function("lens_set_large_struct", |b| {
        b.iter(|| {
            let result = counter_lens.set(black_box(large_struct.clone()), 100);
            black_box(result)
        })
    });

    // Set always benchmarks
    group.bench_function("lens_set_always", |b| {
        b.iter(|| {
            let result = name_lens.set_always(black_box(person.clone()), "Charlie".to_string());
            black_box(result)
        })
    });

    // Modify benchmarks
    group.bench_function("lens_modify_no_change", |b| {
        b.iter(|| {
            let result = age_lens.modify(black_box(person.clone()), |age| age);
            black_box(result)
        })
    });

    group.bench_function("lens_modify_with_change", |b| {
        b.iter(|| {
            let result = age_lens.modify(black_box(person.clone()), |age| age + 1);
            black_box(result)
        })
    });

    group.bench_function("lens_modify_string", |b| {
        b.iter(|| {
            let result =
                name_lens.modify(black_box(person.clone()), |name| format!("Mr. {}", name));
            black_box(result)
        })
    });

    group.bench_function("lens_modify_large_data", |b| {
        b.iter(|| {
            let result = data_lens.modify(black_box(large_struct.clone()), |mut data| {
                data.push(1001);
                data
            });
            black_box(result)
        })
    });

    // Modify always benchmarks
    group.bench_function("lens_modify_always", |b| {
        b.iter(|| {
            let result = age_lens.modify_always(black_box(person.clone()), |age| age + 5);
            black_box(result)
        })
    });

    // Complex modification benchmarks
    group.bench_function("lens_complex_modification", |b| {
        b.iter(|| {
            let result = data_lens.modify(black_box(large_struct.clone()), |mut data| {
                // Perform some computation on the data
                for i in 0..data.len() {
                    data[i] = data[i] * 2 + 1;
                }
                data
            });
            black_box(result)
        })
    });

    // Chained operations benchmarks
    group.bench_function("lens_chained_operations", |b| {
        b.iter(|| {
            let mut result = black_box(person.clone());
            result = name_lens.set(result, "David".to_string());
            result = age_lens.set(result, 40);
            black_box(result)
        })
    });

    // Performance comparison: structural sharing vs always update
    group.bench_function("lens_structural_sharing_benefit", |b| {
        b.iter(|| {
            // This should benefit from structural sharing (same value)
            let result = name_lens.set(black_box(person.clone()), "Alice".to_string());
            black_box(result)
        })
    });

    group.bench_function("lens_no_structural_sharing", |b| {
        b.iter(|| {
            // This always creates new structure
            let result = name_lens.set_always(black_box(person.clone()), "Alice".to_string());
            black_box(result)
        })
    });

    // Benchmarks for metadata field usage
    group.bench_function("lens_metadata_get", |b| {
        b.iter(|| {
            let s = black_box(large_struct.clone());
            let metadata = metadata_lens.get(&s);
            black_box(metadata)
        })
    });

    group.bench_function("lens_metadata_set", |b| {
        b.iter(|| {
            let s = black_box(large_struct.clone());
            let new_metadata = "Updated metadata".to_string();
            let updated = metadata_lens.set(s, new_metadata);
            black_box(updated)
        })
    });

    group.bench_function("lens_metadata_modify", |b| {
        b.iter(|| {
            let s = black_box(large_struct.clone());
            let updated = metadata_lens.modify(s, |meta| format!("{} - modified", meta));
            black_box(updated)
        })
    });

    group.finish();
}
