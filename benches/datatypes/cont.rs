use criterion::{black_box, Criterion};
use rustica::datatypes::cont::Cont;
use std::sync::Arc;

/// Benchmark tests for the Cont (Continuation) monad.
pub fn cont_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Cont");

    // ======== CONSTRUCTION OPERATIONS ========

    // Benchmark cont creation with return_cont (pure)
    group.bench_function("return_cont", |b| {
        b.iter(|| black_box(Cont::<i32, i32>::return_cont(10)));
    });

    // Benchmark cont creation with explicit constructor
    group.bench_function("new", |b| {
        b.iter(|| black_box(Cont::new(|k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| k(42))));
    });

    // ======== CORE OPERATIONS ========

    // Benchmark cont running with identity function
    group.bench_function("run_identity", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().run(|x| x)));
    });

    // Benchmark cont running with transformation
    group.bench_function("run_transform", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().run(|x| x * 2)));
    });

    // Benchmark fmap with simple transformation
    group.bench_function("fmap_simple", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().fmap(|x| x * 2)));
    });

    // Benchmark fmap with complex transformation
    group.bench_function("fmap_complex", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| {
            black_box(cont.clone().fmap(|x| {
                let mut result = 0;
                for i in 0..x {
                    result += i;
                }
                result
            }))
        });
    });

    // Benchmark bind (monadic composition) with simple transformation
    group.bench_function("bind_simple", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| {
            black_box(
                cont.clone()
                    .bind(Arc::new(|x| Cont::<i32, i32>::return_cont(x * 2))),
            )
        });
    });

    // Benchmark bind (monadic composition) with multiple operations
    group.bench_function("bind_chained", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| {
            black_box(
                cont.clone()
                    .bind(Arc::new(|x| Cont::<i32, i32>::return_cont(x + 5)))
                    .bind(Arc::new(|x| Cont::<i32, i32>::return_cont(x * 2))),
            )
        });
    });

    // Benchmark apply
    group.bench_function("apply", |b| {
        let func_cont = Cont::<i32, Arc<dyn Fn(i32) -> i32 + Send + Sync>>::return_cont(Arc::new(
            |x: i32| x * 2,
        )
            as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
        let value_cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(value_cont.clone().apply(func_cont.clone())));
    });

    // Benchmark call_cc (call with current continuation)
    group.bench_function("call_cc_simple", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().call_cc(|k| k(20))));
    });

    // Benchmark call_cc with conditional exit
    group.bench_function("call_cc_conditional", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
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

    // ======== REAL-WORLD USE CASES ========

    // Benchmark error handling pattern
    group.bench_function("error_handling", |b| {
        b.iter(|| {
            let safe_divide = |a: i32, b: i32| -> Cont<i32, i32> {
                if b == 0 {
                    // Early return with error value
                    Cont::new(|_| -1)
                } else {
                    Cont::return_cont(a / b)
                }
            };

            let result = black_box(safe_divide(10, 2).run(|x| x));
            black_box(result)
        });
    });

    // Benchmark nested call_cc for complex control flow
    group.bench_function("nested_call_cc", |b| {
        b.iter(|| {
            let cont = Cont::<i32, i32>::return_cont(10);
            black_box(
                cont.clone()
                    .call_cc(|outer_k| {
                        Cont::<i32, i32>::return_cont(5).call_cc(move |inner_k| {
                            if 5 > 3 {
                                inner_k(15)
                            } else {
                                outer_k(25)
                            }
                        })
                    })
                    .run(|x| x),
            )
        });
    });

    // Benchmark complex continuation chains with type transformations
    group.bench_function("complex_type_transformation", |b| {
        let cont = Cont::<String, i32>::return_cont(10);
        b.iter(|| {
            black_box(
                cont.clone()
                    .bind(Arc::new(|x| Cont::<String, i32>::return_cont(x + 5)))
                    .bind(Arc::new(|x| {
                        if x > 10 {
                            Cont::<String, i32>::return_cont(x * 2)
                        } else {
                            Cont::<String, i32>::return_cont(x)
                        }
                    }))
                    .fmap(|x| x.to_string())
                    .run(|s| format!("Result: {}", s)),
            )
        });
    });

    // Benchmark for a backtracking algorithm pattern
    group.bench_function("backtracking_pattern", |b| {
        b.iter(|| {
            // Simplified backtracking search using continuations
            fn search(choices: Vec<i32>, target: i32, current: i32) -> Cont<bool, bool> {
                if current > target {
                    // Dead end, return false
                    return Cont::return_cont(false);
                }
                if current == target {
                    // Found a solution, return true
                    return Cont::return_cont(true);
                }

                // Try each choice
                Cont::new(move |k| {
                    for choice in choices.iter() {
                        let result = search(choices.clone(), target, current + choice).run(|x| x);
                        if result {
                            return k(true);
                        }
                    }
                    k(false)
                })
            }

            black_box(search(vec![1, 2, 3], 8, 0).run(|x| x))
        });
    });

    // Benchmark for a simple state machine implemented with continuations
    group.bench_function("state_machine", |b| {
        b.iter(|| {
            let initial_state = 0;
            let inputs = vec![1, 2, 3, 4, 5];

            // Define a state transition function
            let transition = |state: i32, input: i32| -> Cont<i32, i32> {
                if input % 2 == 0 {
                    // Even input, double the state
                    Cont::return_cont(state * 2)
                } else {
                    // Odd input, add to the state
                    Cont::return_cont(state + input)
                }
            };

            // Process all inputs in sequence
            let mut current = Cont::<i32, i32>::return_cont(initial_state);
            for input in inputs.iter() {
                let input_val = *input;
                current = current.bind(Arc::new(move |state| transition(state, input_val)));
            }

            black_box(current.run(|final_state| final_state))
        });
    });

    group.finish();
}
