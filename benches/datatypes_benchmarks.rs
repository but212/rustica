use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rustica::datatypes::id::Id;
use rustica::datatypes::maybe::Maybe;
use rustica::datatypes::validated::Validated;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::semigroup::Semigroup;
use smallvec::smallvec;
use std::sync::Arc;

#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "advanced")]
use rustica::datatypes::choice::Choice;
#[cfg(feature = "advanced")]
use rustica::datatypes::cont::Cont;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::State;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::{get, put};
#[cfg(feature = "async")]
use tokio::runtime::Runtime;

fn maybe_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Maybe Operations");

    // Benchmark Maybe::map with reference vs ownership methods
    group.bench_function("maybe_map_ref", |b| {
        let maybe = Maybe::Just(10);
        b.iter(|| black_box(maybe.fmap(|x| x * 2)));
    });

    group.bench_function("maybe_map_owned", |b| {
        b.iter(|| black_box(Maybe::Just(10).fmap_owned(|x| x * 2)));
    });

    // Benchmark Maybe chaining operations
    group.bench_function("maybe_chain", |b| {
        let maybe = Maybe::Just(10);
        b.iter(|| {
            black_box(
                maybe
                    .fmap(|x| x + 5)
                    .bind(|x| {
                        if *x > 10 {
                            Maybe::Just(x * 2)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|x| x.to_string()),
            )
        });
    });

    group.finish();

    // Benchmark for null pointer optimization
    let mut size_group = c.benchmark_group("Maybe Size Optimization");
    size_group.bench_function("maybe_size_check", |b| {
        b.iter(|| {
            // This measures the overhead of constructing and using Maybe
            // which should be minimal due to null pointer optimization
            black_box(std::mem::size_of::<Maybe<u64>>());
            black_box(std::mem::size_of::<Option<u64>>());
        });
    });
    size_group.finish();
}

fn id_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Id Operations");

    // Benchmark Id::map with reference vs ownership
    group.bench_function("id_map_ref", |b| {
        let id = Id::new(10);
        b.iter(|| black_box(id.fmap(|x| x * 2)));
    });

    group.bench_function("id_map_owned", |b| {
        b.iter(|| black_box(Id::new(10).fmap_owned(|x| x * 2)));
    });

    // Benchmark Id chaining operations
    group.bench_function("id_chain", |b| {
        let id = Id::new(10);
        b.iter(|| {
            black_box(
                id.fmap(|x| x + 5)
                    .bind(|x| Id::new(*x * 2))
                    .fmap(|x| x.to_string()),
            )
        });
    });

    group.finish();
}

fn validated_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Validated Operations");

    // Benchmark Validated with small number of errors (SmallVec optimization)
    group.bench_function("validated_smallvec_few_errors", |b| {
        b.iter(|| {
            let validated1 = Validated::<_, i32>::invalid("error 1".to_string());
            let validated2 = Validated::<_, i32>::invalid("error 2".to_string());
            let combined = match (validated1, validated2) {
                (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                    let mut errors = e1;
                    errors.extend(e2.iter().cloned());
                    Validated::Invalid(errors)
                }
                (v @ Validated::Valid(_), _) => v,
                (_, v @ Validated::Valid(_)) => v,
            };
            black_box(combined)
        });
    });

    // Benchmark Validated with larger number of errors (tests SmallVec vs Vec)
    group.bench_function("validated_smallvec_many_errors", |b| {
        b.iter(|| {
            let mut errors = smallvec!["error 1".to_string()];
            for i in 2..11 {
                errors.push(format!("error {}", i));
            }
            let validated = Validated::<_, i32>::Invalid(errors);
            black_box(validated)
        });
    });

    group.finish();
}

#[cfg(feature = "async")]
fn async_monad_benchmarks(c: &mut Criterion) {
    // Create a runtime for executing async tasks
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("AsyncM Operations");

    // Benchmark AsyncM creation performance
    group.bench_function("asyncm_pure_creation", |b| {
        b.iter(|| black_box(AsyncM::pure(10)));
    });

    group.bench_function("asyncm_new_creation", |b| {
        b.iter(|| black_box(AsyncM::new(|| async { 10 })));
    });

    // Benchmark AsyncM::fmap performance (function application)
    group.bench_function("asyncm_fmap", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| {
            let mapped = async_value.clone().fmap(|x| async move { x * 2 });
            // We don't await the future here since we're just benchmarking the creation overhead
            black_box(mapped)
        });
    });

    // Benchmark AsyncM::bind performance (monadic chaining)
    group.bench_function("asyncm_bind", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| {
            let bound = async_value
                .clone()
                .bind(|x| async move { AsyncM::pure(x + 5) });
            black_box(bound)
        });
    });

    // Benchmark AsyncM execution performance for a simple value
    group.bench_function("asyncm_execute_pure", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| rt.block_on(async { black_box(async_value.clone().try_get().await) }));
    });

    // Benchmark AsyncM execution performance for a more complex chain
    group.bench_function("asyncm_execute_chain", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| {
            rt.block_on(async {
                let result = async_value
                    .clone()
                    .fmap(|x| async move { x + 5 })
                    .bind(|x| async move { AsyncM::pure(x * 2) })
                    .bind(|x| async move { AsyncM::pure(x - 1) })
                    .try_get()
                    .await;
                black_box(result)
            })
        });
    });

    // Benchmark AsyncM error handling
    group.bench_function("asyncm_result_handling", |b| {
        b.iter(|| {
            let result_async = AsyncM::from_result_or_default(
                || async {
                    if black_box(true) {
                        Ok(42)
                    } else {
                        Err("error")
                    }
                },
                0,
            );
            black_box(result_async)
        });
    });

    group.finish();

    // Benchmark memory overhead
    let mut size_group = c.benchmark_group("AsyncM Size Optimization");
    size_group.bench_function("asyncm_size_check", |b| {
        b.iter(|| {
            // Measure the size of AsyncM compared to basic future wrappers
            black_box(std::mem::size_of::<AsyncM<i32>>());
            black_box(std::mem::size_of::<Arc<dyn Fn() -> i32 + Send + Sync>>());
        });
    });
    size_group.finish();
}

#[cfg(feature = "advanced")]
fn cont_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Cont Operations");

    // Benchmark cont creation
    group.bench_function("cont_return_cont", |b| {
        b.iter(|| black_box(Cont::<i32, i32>::return_cont(10)));
    });

    // Benchmark cont running with identity
    group.bench_function("cont_run_identity", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().run(|x| x)));
    });

    // Benchmark cont running with transformation
    group.bench_function("cont_run_transform", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().run(|x| x * 2)));
    });

    // Benchmark cont mapping
    group.bench_function("cont_fmap", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().fmap(|x| x * 2)));
    });

    // Benchmark cont binding (monadic composition)
    group.bench_function("cont_bind", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| {
            black_box(cont.clone().bind(std::sync::Arc::new(|x| {
                Cont::<i32, i32>::return_cont(x * 2)
            })))
        });
    });

    // Benchmark cont_call_cc (capturing continuations)
    group.bench_function("cont_call_cc", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| black_box(cont.clone().call_cc(|k| k(20))));
    });

    // Benchmark complex continuation chains
    group.bench_function("cont_complex_chain", |b| {
        let cont = Cont::<i32, i32>::return_cont(10);
        b.iter(|| {
            black_box(
                cont.clone()
                    .bind(std::sync::Arc::new(|x| {
                        Cont::<i32, i32>::return_cont(x + 5)
                    }))
                    .bind(std::sync::Arc::new(|x| {
                        if x > 10 {
                            Cont::<i32, i32>::return_cont(x * 2)
                        } else {
                            Cont::<i32, i32>::return_cont(x)
                        }
                    }))
                    .fmap(|x| x.to_string())
                    .run(|s| s.len() as i32),
            )
        });
    });

    group.finish();
}

#[cfg(feature = "advanced")]
fn state_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("State Operations");

    // Benchmark state creation and running with simple state
    group.bench_function("state_creation_run", |b| {
        b.iter(|| {
            let state = State::pure(5);
            black_box(state.run_state(10))
        });
    });

    // Benchmark get and put operations
    group.bench_function("state_get_put", |b| {
        b.iter(|| {
            let state = get::<i32>().bind(|s| put(s + 1));
            black_box(state.run_state(5))
        });
    });

    // Benchmark state mapping
    group.bench_function("state_fmap", |b| {
        let state = State::pure(5);
        b.iter(|| black_box(state.clone().fmap(|x| x * 2).run_state(10)));
    });

    // Benchmark state binding
    group.bench_function("state_bind", |b| {
        let state = State::pure(5);
        b.iter(|| black_box(state.clone().bind(|x| State::pure(x * 2)).run_state(10)));
    });

    // Benchmark complex state chain
    group.bench_function("state_complex_chain", |b| {
        b.iter(|| {
            let state = get::<i32>()
                .bind(|s| {
                    State::pure(s * 2)
                        .bind(|x| put(x + 5))
                        .bind(|_| get::<i32>())
                })
                .fmap(|x| x + 1);

            black_box(state.run_state(10))
        });
    });

    group.finish();
}

#[cfg(feature = "advanced")]
fn choice_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Choice Operations");

    // Benchmark choice creation
    group.bench_function("choice_creation", |b| {
        b.iter(|| black_box(Choice::new(5, vec![])));
    });

    // Benchmark choice mapping
    group.bench_function("choice_fmap", |b| {
        let choice = Choice::new(5, vec![]);
        b.iter(|| black_box(choice.fmap(|x| x * 2)));
    });

    // Benchmark choice binding
    group.bench_function("choice_bind", |b| {
        let choice = Choice::new(5, vec![]);
        b.iter(|| black_box(choice.bind(|x| Choice::new(x * 2, vec![]))));
    });

    // Benchmark alternation between choices
    group.bench_function("choice_alternation", |b| {
        let first = Choice::new(5, vec![]);
        let second = Choice::new(10, vec![]);
        b.iter(|| black_box(first.combine(&second)));
    });

    // Benchmark combine operations on different choice variants
    group.bench_function("choice_combine_operations", |b| {
        b.iter(|| {
            let first = Choice::new(5, vec![]);
            let second = Choice::new(10, vec![]);
            let result1 = first.clone().fmap(|x| x * 2); // Choice with first value 10
            let result2 = second.clone().fmap(|x| x * 2); // Choice with first value 20
            black_box((result1, result2))
        });
    });

    group.finish();
}

#[cfg(not(feature = "async"))]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    async_monad_benchmarks,
);

#[cfg(not(feature = "async"))]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
    async_monad_benchmarks,
);

criterion_main!(datatype_benches);
