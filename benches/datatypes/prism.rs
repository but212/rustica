use crate::harness::{BenchGroup, Harness};
use rustica::datatypes::prism::Prism;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
enum Status {
    Active(String),
    Inactive,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(dead_code)]
enum Level1 {
    Next(Level2),
    Other,
}

#[derive(Clone, Debug, PartialEq)]
#[allow(dead_code)]
enum Level2 {
    Next(Level3),
    Other,
}

#[derive(Clone, Debug, PartialEq)]
enum Level3 {
    Value(String),
    #[allow(dead_code)]
    Other,
}

fn bench_timing(group: &mut BenchGroup) {
    let active_status = Status::Active("Alice".to_string());
    let inactive_status = Status::Inactive;

    let active_prism = Prism::new(
        |s: &Status| match s {
            Status::Active(name) => Some(name),
            _ => None,
        },
        Status::Active,
    );

    // 1. Preview operations
    group.bench_fn("direct_borrow_baseline", || {
        black_box(match &active_status {
            Status::Active(name) => Some(name.as_str()),
            _ => None,
        });
    });

    group.bench_fn("preview_hit", || {
        black_box(active_prism.preview(black_box(&active_status)));
    });

    group.bench_fn("preview_miss", || {
        black_box(active_prism.preview(black_box(&inactive_status)));
    });

    group.bench_fn("to_value_hit", || {
        black_box(active_prism.to_value(black_box(&active_status)));
    });

    // 2. Set operations
    group.bench_fn("set_same_value", || {
        black_box(active_prism.set(black_box(active_status.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_always_same_value", || {
        black_box(active_prism.set_always(black_box(active_status.clone()), "Alice".to_string()));
    });

    group.bench_fn("set_hit", || {
        black_box(active_prism.set(black_box(active_status.clone()), "Bob".to_string()));
    });

    group.bench_fn("set_miss", || {
        black_box(active_prism.set(black_box(inactive_status.clone()), "Bob".to_string()));
    });

    // 3. Modify operations
    group.bench_fn("modify_same_value", || {
        black_box(active_prism.modify(black_box(active_status.clone()), |name| name));
    });

    group.bench_fn("modify_always_same_value", || {
        black_box(active_prism.modify_always(black_box(active_status.clone()), |name| name));
    });

    group.bench_fn("modify_hit", || {
        black_box(active_prism.modify(black_box(active_status.clone()), |name| name + "!"));
    });

    // 4. Multi-level composition
    let l1_prism = Prism::new(
        |l: &Level1| match l {
            Level1::Next(l2) => Some(l2),
            _ => None,
        },
        Level1::Next,
    );

    let l2_prism = Prism::new(
        |l: &Level2| match l {
            Level2::Next(l3) => Some(l3),
            _ => None,
        },
        Level2::Next,
    );

    let l3_prism = Prism::new(
        |l: &Level3| match l {
            Level3::Value(val) => Some(val),
            _ => None,
        },
        Level3::Value,
    );

    let deep_prism = l1_prism.then(l2_prism).then(l3_prism);

    let deep_target = Level1::Next(Level2::Next(Level3::Value("nested_leaf".to_string())));

    group.bench_fn("composed_3level_preview_hit", || {
        black_box(deep_prism.preview(black_box(&deep_target)));
    });

    group.bench_fn("composed_3level_set_same_value", || {
        black_box(deep_prism.set(black_box(deep_target.clone()), "nested_leaf".to_string()));
    });

    group.bench_fn("composed_3level_set_hit", || {
        black_box(deep_prism.set(black_box(deep_target.clone()), "updated_leaf".to_string()));
    });
}

fn bench_memory(group: &mut BenchGroup) {
    let active_status = Status::Active("Alice".to_string());

    let active_prism = Prism::new(
        |s: &Status| match s {
            Status::Active(name) => Some(name),
            _ => None,
        },
        Status::Active,
    );

    group.bench_memory(
        "preview_hit",
        || Some(active_status.clone()),
        |state| {
            let s = state.take().unwrap();
            black_box(active_prism.preview(&s));
        },
    );

    group.bench_memory(
        "to_value_hit",
        || Some(active_status.clone()),
        |state| {
            let s = state.take().unwrap();
            black_box(active_prism.to_value(&s));
        },
    );

    group.bench_memory(
        "set_same_value",
        || Some((active_status.clone(), "Alice".to_string())),
        |state| {
            let (s, val) = state.take().unwrap();
            black_box(active_prism.set(s, val));
        },
    );

    group.bench_memory(
        "set_always_same_value",
        || Some((active_status.clone(), "Alice".to_string())),
        |state| {
            let (s, val) = state.take().unwrap();
            black_box(active_prism.set_always(s, val));
        },
    );

    group.bench_memory(
        "set_hit",
        || Some((active_status.clone(), "Bob".to_string())),
        |state| {
            let (s, val) = state.take().unwrap();
            black_box(active_prism.set(s, val));
        },
    );

    group.bench_memory(
        "modify_same_value",
        || Some(active_status.clone()),
        |state| {
            let s = state.take().unwrap();
            black_box(active_prism.modify(s, |name| name));
        },
    );

    let l1_prism = Prism::new(
        |l: &Level1| match l {
            Level1::Next(l2) => Some(l2),
            _ => None,
        },
        Level1::Next,
    );

    let l2_prism = Prism::new(
        |l: &Level2| match l {
            Level2::Next(l3) => Some(l3),
            _ => None,
        },
        Level2::Next,
    );

    let l3_prism = Prism::new(
        |l: &Level3| match l {
            Level3::Value(val) => Some(val),
            _ => None,
        },
        Level3::Value,
    );

    let deep_prism = l1_prism.then(l2_prism).then(l3_prism);

    let deep_target = Level1::Next(Level2::Next(Level3::Value("nested_leaf".to_string())));

    group.bench_memory(
        "composed_3level_preview_hit",
        || Some(deep_target.clone()),
        |state| {
            let s = state.take().unwrap();
            black_box(deep_prism.preview(&s));
        },
    );

    group.bench_memory(
        "composed_3level_set_same_value",
        || Some((deep_target.clone(), "nested_leaf".to_string())),
        |state| {
            let (s, val) = state.take().unwrap();
            black_box(deep_prism.set(s, val));
        },
    );
}

pub fn prism_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Prism");
    bench_timing(&mut group);
    bench_memory(&mut group);
}
