use crate::harness::Harness;
use rustica::datatypes::free::{AnyValue, Free};
use std::hint::black_box;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum CalcOp {
    Add(i32),
    Get,
}

impl CalcOp {
    fn add(n: i32) -> Free<Self, ()> {
        Free::suspend(Self::Add(n))
    }

    fn get() -> Free<Self, i32> {
        Free::suspend(Self::Get)
    }
}

fn build_free_chain(depth: usize) -> Free<CalcOp, i32> {
    let mut program: Free<CalcOp, ()> = CalcOp::add(1);
    for _ in 1..depth.saturating_sub(1) {
        program = program.then(CalcOp::add(1));
    }
    program.then(CalcOp::get())
}

pub fn free_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Free");

    for depth in [10, 100] {
        group.bench_with_input("build_chain", &depth, |&depth| {
            black_box(build_free_chain(depth));
        });

        group.bench_with_input("build_and_run", &depth, |&depth| {
            let program = build_free_chain(depth);
            let mut state = 0;
            let result: i32 = program.run(|op| match op {
                CalcOp::Add(n) => {
                    state += n;
                    Arc::new(()) as AnyValue
                },
                CalcOp::Get => Arc::new(state) as AnyValue,
            });
            black_box(result);
        });
    }
}
