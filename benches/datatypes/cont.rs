use criterion::{black_box, Criterion};
use rustica::datatypes::cont::Cont;
use std::sync::Arc;

/// Benchmark tests for the Cont (Continuation) monad.
pub fn cont_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Cont");

    // Construction operations
    group.bench_function("return_cont", |b| {
        b.iter(|| black_box(Cont::<i32, i32>::return_cont(10)));
    });

    group.bench_function("new", |b| {
        b.iter(|| black_box(Cont::new(|k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| k(42))));
    });

    // Core operations
    let cont = Cont::<i32, i32>::return_cont(10);

    group.bench_function("run", |b| {
        b.iter(|| black_box(cont.clone().run(|x| x * 2)));
    });

    group.bench_function("fmap", |b| {
        b.iter(|| black_box(cont.clone().fmap(|x| x * 2)));
    });

    group.bench_function("bind", |b| {
        b.iter(|| black_box(cont.clone().bind(Arc::new(|x| Cont::<i32, i32>::return_cont(x * 2)))));
    });

    group.bench_function("apply", |b| {
        let func_cont = Cont::<i32, Arc<dyn Fn(i32) -> i32 + Send + Sync>>::return_cont(Arc::new(
            |x: i32| x * 2,
        )
            as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
        b.iter(|| black_box(cont.clone().apply(func_cont.clone())));
    });

    group.bench_function("call_cc", |b| {
        b.iter(|| {
            black_box(cont.clone().call_cc(|k| {
                if 10 > 5 {
                    k(20)
                } else {
                    Cont::<i32, i32>::return_cont(30)
                }
            }))
        });
    });

    // Real-world use cases
    group.bench_function("error_handling", |b| {
        let safe_divide = |a: i32, b: i32| -> Cont<i32, i32> {
            if b == 0 {
                Cont::new(|_| -1)
            } else {
                Cont::return_cont(a / b)
            }
        };
        b.iter(|| black_box(safe_divide(10, 2).run(|x| x)));
    });

    group.bench_function("state_machine", |b| {
        b.iter(|| {
            let inputs = [1, 2, 3, 4, 5];
            let transition = |state: i32, input: i32| -> Cont<i32, i32> {
                if input % 2 == 0 {
                    Cont::return_cont(state * 2)
                } else {
                    Cont::return_cont(state + input)
                }
            };

            let mut current = Cont::<i32, i32>::return_cont(0);
            for input in inputs.iter() {
                let input_val = *input;
                current = current.bind(Arc::new(move |state| transition(state, input_val)));
            }

            black_box(current.run(|final_state| final_state))
        });
    });

    group.bench_function("continuation_composition", |b| {
        b.iter(|| {
            // Chain multiple continuations to simulate a pipeline
            let step1 = Cont::<i32, i32>::return_cont(10);
            let step2 = step1.bind(Arc::new(|x| Cont::return_cont(x + 5)));
            let step3 = step2.bind(Arc::new(|x| Cont::return_cont(x * 2)));
            let step4 = step3.bind(Arc::new(|x| {
                if x > 20 {
                    Cont::return_cont(x - 10)
                } else {
                    Cont::return_cont(x)
                }
            }));

            black_box(step4.run(|x| x))
        });
    });

    group.bench_function("backtracking", |b| {
        b.iter(|| {
            fn search(choices: Vec<i32>, target: i32, current: i32) -> Cont<bool, bool> {
                if current > target {
                    return Cont::return_cont(false);
                }
                if current == target {
                    return Cont::return_cont(true);
                }

                Cont::new(move |k| {
                    for choice in choices.iter() {
                        if search(choices.clone(), target, current + choice).run(|x| x) {
                            return k(true);
                        }
                    }
                    k(false)
                })
            }
            black_box(search(vec![1, 2, 3], 8, 0).run(|x| x))
        });
    });

    group.finish();
}
