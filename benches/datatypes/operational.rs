use crate::harness::{BenchGroup, Harness};
use rustica::datatypes::operational::{Command, Handler, Program};
use std::hint::black_box;

static OPERATIONAL_MEMORY_DEPTHS: [usize; 3] = [10, 100, 1000];
static OPERATIONAL_DEPTHS: [usize; 4] = [10, 100, 1000, 5000];

struct Add(i32);
impl Command for Add {
    type Output = ();
}

struct Get;
impl Command for Get {
    type Output = i32;
}

struct Calculator {
    current: i32,
}

impl Handler<Add> for Calculator {
    fn handle(&mut self, cmd: Add) {
        self.current += cmd.0;
    }
}

impl Handler<Get> for Calculator {
    fn handle(&mut self, _cmd: Get) -> i32 {
        self.current
    }
}

fn build_operational_chain(depth: usize) -> Program<Calculator, i32> {
    let mut program: Program<Calculator, ()> = Add(1).suspend();
    for _ in 1..depth.saturating_sub(1) {
        program = program.then(Add(1).suspend());
    }
    program.then(Get.suspend())
}

fn build_mixed_operational_chain(depth: usize) -> Program<Calculator, ()> {
    let mut program: Program<Calculator, ()> = Add(1).suspend();
    // Each level wraps the accumulated chain on both sides to reproduce mixed association.
    for _ in 1..depth {
        program = Add(1).suspend().then(program.then(Add(1).suspend()));
    }
    program
}

fn configure_depth_sampling(group: &mut BenchGroup, depth: usize) {
    if depth >= 1000 {
        group.batch_iters(1).measure_iters(100);
    } else {
        group.reset_sampling();
    }
}

/// Measures cumulative heap allocation churn for Program::run across varying tree depths.
fn bench_memory_churn(group: &mut BenchGroup) {
    group.reset_sampling();
    group.measure_iters(50);
    group.clear_throughput();

    for &depth in &OPERATIONAL_MEMORY_DEPTHS {
        let name = format!("memory_churn/{depth}");
        group.bench_memory(
            &name,
            || Some(build_operational_chain(depth)),
            |prog_opt| {
                let prog = prog_opt.take().expect("program initialized in setup");
                let mut calc = Calculator { current: 0 };
                black_box(prog.run(&mut calc));
            },
        );
    }
}

pub fn operational_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Operational");

    for &depth in &OPERATIONAL_DEPTHS {
        configure_depth_sampling(&mut group, depth);
        group.bench_with_input("build_chain", &depth, |&depth| {
            // Includes dropping the completed program after construction.
            black_box(build_operational_chain(depth));
        });

        let build_name = format!("build_only/{depth}");
        group.bench_build(&build_name, || build_operational_chain(depth));

        group.bench_with_input("build_and_run", &depth, |&depth| {
            let program = build_operational_chain(depth);
            let mut calc = Calculator { current: 0 };
            let result = program.run(&mut calc);
            black_box(result);
        });

        let run_name = format!("run_chain/{depth}");
        group.bench_batched(
            &run_name,
            || Some(build_operational_chain(depth)),
            |program| {
                let program = program.take().expect("program initialized in setup");
                let mut calc = Calculator { current: 0 };
                black_box(program.run(&mut calc));
            },
        );

        let drop_name = format!("drop_chain/{depth}");
        group.bench_batched(
            &drop_name,
            || Some(build_operational_chain(depth)),
            |program| {
                let program = program.take().expect("program initialized in setup");
                drop(program);
            },
        );

        let mixed_build_name = format!("mixed_build_only/{depth}");
        group.bench_build(&mixed_build_name, || build_mixed_operational_chain(depth));

        let mixed_run_name = format!("mixed_run_chain/{depth}");
        group.bench_batched(
            &mixed_run_name,
            || Some(build_mixed_operational_chain(depth)),
            |program| {
                let program = program.take().expect("program initialized in setup");
                let mut calc = Calculator { current: 0 };
                program.run(&mut calc);
                black_box(());
            },
        );

        let mixed_drop_name = format!("mixed_drop_chain/{depth}");
        group.bench_batched(
            &mixed_drop_name,
            || Some(build_mixed_operational_chain(depth)),
            |program| {
                let program = program.take().expect("program initialized in setup");
                drop(program);
            },
        );
    }

    bench_memory_churn(&mut group);
}
