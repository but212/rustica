use crate::harness::{BenchGroup, Harness};
use rustica::datatypes::operational::{Command, Handler, Program};
use std::hint::black_box;

static OPERATIONAL_MEMORY_DEPTHS: [usize; 3] = [10, 100, 1000];

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

    for depth in [10, 100] {
        group.bench_with_input("build_chain", &depth, |&depth| {
            black_box(build_operational_chain(depth));
        });

        group.bench_with_input("build_and_run", &depth, |&depth| {
            let program = build_operational_chain(depth);
            let mut calc = Calculator { current: 0 };
            let result = program.run(&mut calc);
            black_box(result);
        });
    }

    bench_memory_churn(&mut group);
}
