use crate::harness::Harness;
use rustica::datatypes::operational::{Command, Handler, Program};
use std::hint::black_box;

struct Add(i32);
impl Command for Add {
    type Output = ();
}

#[allow(dead_code)]
struct Multiply(i32);
impl Command for Multiply {
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

impl Handler<Multiply> for Calculator {
    fn handle(&mut self, cmd: Multiply) {
        self.current *= cmd.0;
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
}
