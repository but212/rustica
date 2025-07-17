use criterion::Criterion;
use rustica::datatypes::state::State;
use rustica::datatypes::state::{get, modify, put};
use std::hint::black_box;

pub fn state_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("State");

    group.bench_function("creation_and_run", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(5));
        });
    });

    group.bench_function("get", |b| {
        b.iter(|| {
            let state = get::<i32>();
            black_box(state.run_state(10));
        });
    });

    group.bench_function("put", |b| {
        b.iter(|| {
            let state = put(42);
            black_box(state.run_state(10));
        });
    });

    group.bench_function("modify", |b| {
        b.iter(|| {
            let state = modify(|s: i32| s * 2);
            black_box(state.run_state(10));
        });
    });

    group.bench_function("bind_chain", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            let computation = state
                .bind(|x| State::pure(x * 2))
                .bind(|x| State::pure(x + 10));
            black_box(computation.run_state(0));
        });
    });

    group.finish();
}
