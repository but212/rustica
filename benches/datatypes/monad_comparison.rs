use crate::harness::Harness;
use rustica::datatypes::free::{AnyValue, Free};
use rustica::datatypes::operational::{Command, Handler, Program};
use std::hint::black_box;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum FreeOp {
    Add(i32),
    Get,
}

fn run_free(depth: usize) -> i32 {
    let mut prog: Free<FreeOp, ()> = Free::suspend(FreeOp::Add(1));
    for _ in 1..depth.saturating_sub(1) {
        prog = prog.then(Free::suspend(FreeOp::Add(1)));
    }
    let full = prog.then(Free::suspend(FreeOp::Get));

    let mut state = 0;
    full.run(|op| match op {
        FreeOp::Add(n) => {
            state += n;
            Arc::new(()) as AnyValue
        },
        FreeOp::Get => Arc::new(state) as AnyValue,
    })
}

struct OpAdd(i32);
impl Command for OpAdd {
    type Output = ();
}

struct OpGet;
impl Command for OpGet {
    type Output = i32;
}

struct OpCalc {
    current: i32,
}

impl Handler<OpAdd> for OpCalc {
    fn handle(&mut self, cmd: OpAdd) {
        self.current += cmd.0;
    }
}

impl Handler<OpGet> for OpCalc {
    fn handle(&mut self, _cmd: OpGet) -> i32 {
        self.current
    }
}

fn run_operational(depth: usize) -> i32 {
    let mut prog: Program<OpCalc, ()> = OpAdd(1).suspend();
    for _ in 1..depth.saturating_sub(1) {
        prog = prog.then(OpAdd(1).suspend());
    }
    let full = prog.then(OpGet.suspend());

    let mut calc = OpCalc { current: 0 };
    full.run(&mut calc)
}

#[derive(Clone, Copy)]
enum DslOp {
    Add(i32),
    Get,
}

fn run_dsl_loop(depth: usize) -> i32 {
    let mut ops = Vec::with_capacity(depth);
    for _ in 0..depth.saturating_sub(1) {
        ops.push(DslOp::Add(1));
    }
    ops.push(DslOp::Get);

    let mut state = 0;
    for op in ops {
        match op {
            DslOp::Add(n) => state += n,
            DslOp::Get => return state,
        }
    }
    state
}

pub fn monad_comparison_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("MonadComparison");

    for depth in [10, 100] {
        group.bench_with_input("free_build_and_run", &depth, |&depth| {
            black_box(run_free(depth));
        });

        group.bench_with_input("program_build_and_run", &depth, |&depth| {
            black_box(run_operational(depth));
        });

        group.bench_with_input("dsl_loop", &depth, |&depth| {
            black_box(run_dsl_loop(depth));
        });
    }
}
