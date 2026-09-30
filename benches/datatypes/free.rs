use crate::harness::{BenchGroup, Harness, Throughput};
use rustica::datatypes::free::{AnyValue, Free};
use std::hint::black_box;
use std::sync::Arc;

static BASELINE_DEPTHS: [usize; 2] = [10, 100];
static BENCH_DEPTHS: [usize; 4] = [10, 100, 1000, 5000];
static MEMORY_DEPTHS: [usize; 3] = [10, 100, 1000];

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

fn build_then_chain(depth: usize) -> Free<CalcOp, i32> {
    let mut program: Free<CalcOp, ()> = CalcOp::add(1);
    for _ in 1..depth.saturating_sub(1) {
        program = program.then(CalcOp::add(1));
    }
    program.then(CalcOp::get())
}

fn build_bind_chain(depth: usize) -> Free<CalcOp, i32> {
    let mut program: Free<CalcOp, ()> = CalcOp::add(1);
    for _ in 1..depth.saturating_sub(1) {
        program = program.and_then(|_| CalcOp::add(1));
    }
    program.and_then(|_| CalcOp::get())
}

fn run_calc(program: &Free<CalcOp, i32>) -> i32 {
    let mut state = 0;
    program.run(|op| match op {
        CalcOp::Add(n) => {
            state += n;
            Arc::new(()) as AnyValue
        },
        CalcOp::Get => Arc::new(state) as AnyValue,
    })
}

fn configure_depth_sampling(group: &mut BenchGroup, depth: usize) {
    if depth >= 1000 {
        group.batch_iters(1).measure_iters(100);
    } else {
        group.reset_sampling();
    }
    group.throughput(Throughput::Elements(depth as u64));
}

/// Baseline benchmarks for chain construction and execution.
fn bench_baseline(group: &mut BenchGroup) {
    for &depth in &BASELINE_DEPTHS {
        group.bench_with_input("build_chain", &depth, |&depth| {
            black_box(build_then_chain(depth));
        });

        group.bench_with_input("build_and_run", &depth, |&depth| {
            let program = build_then_chain(depth);
            let result = run_calc(&program);
            black_box(result);
        });
    }
}

/// Compares construction and execution scaling between `then` and `and_then` chains.
fn bench_sequencing_scaling(group: &mut BenchGroup) {
    for &depth in &BENCH_DEPTHS {
        configure_depth_sampling(group, depth);

        group.bench_with_input("build_then", &depth, |&depth| {
            black_box(build_then_chain(depth));
        });

        group.bench_with_input("build_bind", &depth, |&depth| {
            black_box(build_bind_chain(depth));
        });
    }

    for &depth in &BENCH_DEPTHS {
        configure_depth_sampling(group, depth);

        let then_program = build_then_chain(depth);
        let bind_program = build_bind_chain(depth);

        group.bench_with_input("run_then", &depth, |_| {
            black_box(run_calc(&then_program));
        });

        group.bench_with_input("run_bind", &depth, |_| {
            black_box(run_calc(&bind_program));
        });
    }
}

/// Measures cumulative heap allocation churn across tree depths.
fn bench_memory_churn(group: &mut BenchGroup) {
    for &depth in &MEMORY_DEPTHS {
        group.reset_sampling();
        group.measure_iters(50);
        group.clear_throughput();

        let bench_name = format!("memory_churn/{depth}");
        group.bench_memory(
            &bench_name,
            || build_then_chain(depth),
            |program| {
                black_box(run_calc(program));
            },
        );
    }
}

pub fn free_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Free");

    bench_baseline(&mut group);
    bench_sequencing_scaling(&mut group);
    bench_memory_churn(&mut group);
}
