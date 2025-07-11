use criterion::Criterion;
use rustica::datatypes::state::State;
use rustica::datatypes::state::{get, modify, put};
use std::hint::black_box;

pub fn state_benchmarks(c: &mut Criterion) {
    // Basic operations
    c.bench_function("state_create_and_run", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(5))
        });
    });

    // Core operations
    c.bench_function("state_get", |b| {
        b.iter(|| {
            let state = get::<i32>();
            black_box(state.run_state(10))
        });
    });

    c.bench_function("state_put", |b| {
        b.iter(|| {
            let state = put(42);
            black_box(state.run_state(10))
        });
    });

    c.bench_function("state_modify", |b| {
        b.iter(|| {
            let state = modify(|s: i32| s * 2);
            black_box(state.run_state(10))
        });
    });

    // Monad operations
    c.bench_function("state_bind", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            black_box(
                state
                    .bind(|x: i32| State::pure(x * 2))
                    .bind(|x: i32| State::pure(x + 10)),
            )
        });
    });
}
