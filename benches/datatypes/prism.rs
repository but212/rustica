use crate::harness::Harness;
use rustica::datatypes::prism::Prism;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
enum Status {
    Active(String),
    Inactive,
}

pub fn prism_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Prism");

    let active_status = Status::Active("Alice".to_string());
    let inactive_status = Status::Inactive;

    let active_prism = Prism::new(
        |s: &Status| match s {
            Status::Active(name) => Some(name.clone()),
            _ => None,
        },
        Status::Active,
    );

    group.bench_fn("preview_hit", || {
        black_box(active_prism.preview(black_box(&active_status)));
    });

    group.bench_fn("preview_miss", || {
        black_box(active_prism.preview(black_box(&inactive_status)));
    });

    group.bench_fn("modify_same_value", || {
        black_box(active_prism.modify(black_box(active_status.clone()), |name| name));
    });

    group.bench_fn("modify_different_value", || {
        black_box(active_prism.modify(black_box(active_status.clone()), |name| name + "!"));
    });

    group.bench_fn("set_if_different_same", || {
        black_box(
            active_prism.set_if_different(black_box(active_status.clone()), "Alice".to_string()),
        );
    });

    group.bench_fn("set_if_different_changed", || {
        black_box(
            active_prism.set_if_different(black_box(active_status.clone()), "Bob".to_string()),
        );
    });
}
