use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rustica::datatypes::either::Either;
use rustica::datatypes::id::Id;
use rustica::datatypes::lens::Lens;
use rustica::datatypes::maybe::Maybe;
use rustica::datatypes::prism::Prism;
use rustica::datatypes::reader::Reader;
use rustica::datatypes::validated::Validated;
use rustica::datatypes::wrapper::boxed_fn::BoxedFn;
use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::datatypes::wrapper::value::Value;
use rustica::datatypes::writer::Writer;
use rustica::traits::applicative::Applicative;
use rustica::traits::evaluate::Evaluate;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::pure::Pure;
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
use rustica::datatypes::io::IO;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::State;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::{get, put};
#[cfg(feature = "async")]
use tokio::runtime::Runtime;

/// A log type for benchmarking Writer performance
#[derive(Clone, Debug, PartialEq)]
struct Log(Vec<String>);

impl Semigroup for Log {
    fn combine(&self, other: &Self) -> Self {
        let mut combined = self.0.clone();
        combined.extend(other.0.clone());
        Log(combined)
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut combined = self.0;
        combined.extend(other.0);
        Log(combined)
    }
}

impl Monoid for Log {
    fn empty() -> Self {
        Log(Vec::new())
    }
}

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

    // Benchmark reference efficiency
    group.bench_function("id_from_ref", |b| {
        let value = 42;
        b.iter(|| black_box(Id::from_ref(&value)));
    });

    // Benchmark value creation vs cloning
    group.bench_function("id_new_vs_clone", |b| {
        let id = Id::new(10);
        b.iter_batched(
            || (),
            |_| {
                let new = Id::new(10);
                let cloned = id.clone();
                black_box((new, cloned))
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // Benchmark const fn
    group.bench_function("id_const_new", |b| {
        b.iter(|| {
            // This tests the compile-time optimization of const fn
            // The actual benchmark measures runtime overhead
            black_box(Id::new(10).into_inner())
        });
    });

    // Benchmark ownership transfer
    group.bench_function("id_then_composition", |b| {
        let id = Id::new(10);
        b.iter(|| black_box(id.fmap(|x| x + 1).then(Id::new(20)).fmap(|x| x * 2)));
    });

    // Benchmark Default implementation
    group.bench_function("id_default", |b| {
        b.iter(|| black_box(Id::<String>::default()));
    });

    // Benchmark applicative operations
    group.bench_function("id_applicative", |b| {
        let id1 = Id::new(10);
        let id2 = Id::new(5);
        let f = |a: &i32, b: &i32| a + b;
        b.iter(|| black_box(id1.lift2(&id2, &f)));
    });

    // Benchmark non-copy types with Id
    group.bench_function("id_non_copy_types", |b| {
        let s = "Hello, world!".to_string();
        b.iter(|| black_box(Id::new(s.clone()).fmap(|s| s.to_owned() + " More text!")));
    });

    group.finish();
}

fn validated_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Validated Operations");

    // Benchmark Validated with small number of errors (SmallVec optimization)
    group.bench_function("validated_smallvec_few_errors", |b| {
        b.iter(|| {
            let validated1 = Validated::<_, i32>::SingleInvalid("error 1".to_string());
            let validated2 = Validated::<_, i32>::SingleInvalid("error 2".to_string());
            let combined = match (validated1, validated2) {
                (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                    let mut errors = smallvec![e1];
                    errors.push(e2);
                    Validated::MultiInvalid(errors)
                }
                (Validated::SingleInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors = e2;
                    errors.insert(0, e1);
                    Validated::MultiInvalid(errors)
                }
                (Validated::MultiInvalid(e1), Validated::SingleInvalid(e2)) => {
                    let mut errors = e1;
                    errors.push(e2);
                    Validated::MultiInvalid(errors)
                }
                (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors = e1;
                    errors.extend(e2);
                    Validated::MultiInvalid(errors)
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
            let validated = Validated::<_, i32>::MultiInvalid(errors);
            black_box(validated)
        });
    });

    // Benchmark Validated creation (valid case)
    group.bench_function("validated_create_valid", |b| {
        b.iter(|| black_box(Validated::<String, _>::valid(42)));
    });

    // Benchmark Validated creation (invalid case)
    group.bench_function("validated_create_invalid", |b| {
        b.iter(|| black_box(Validated::<_, i32>::invalid("validation error".to_string())));
    });

    // Benchmark Validated fmap operation
    group.bench_function("validated_fmap", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.clone().fmap(|x| x * 2));
            let result2 = black_box(invalid.clone().fmap(|x| x * 2));
            (result1, result2)
        });
    });

    // Benchmark Validated bind operation
    group.bench_function("validated_bind", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.bind(|x| Validated::<String, _>::valid(x * 2)));
            let result2 = black_box(invalid.bind(|x| Validated::<String, _>::valid(x * 2)));
            (result1, result2)
        });
    });

    // Benchmark Validated pure operation
    group.bench_function("validated_pure", |b| {
        b.iter(|| {
            let value = 42;
            black_box(Validated::<String, i32>::pure(&value))
        });
    });

    // Benchmark Validated apply operation
    group.bench_function("validated_apply", |b| {
        // The function should take a reference to i32
        let add_one = |x: &i32| x + 1;
        let valid_fn: Validated<String, _> = Validated::valid(add_one);
        let valid_value: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid_value.clone().apply(&valid_fn));
            let result2 = black_box(invalid.clone().apply(&valid_fn));
            (result1, result2)
        });
    });

    // Benchmark Validated fold operation
    group.bench_function("validated_fold", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.fold_left(&0, |acc, x| acc + x));
            let result2 = black_box(invalid.fold_left(&0, |acc, x| acc + x));
            (result1, result2)
        });
    });

    // Benchmark Validated errors retrieval
    group.bench_function("validated_errors", |b| {
        let single_error: Validated<String, i32> = Validated::invalid("error".to_string());
        let mut multi_errors = smallvec!["error 1".to_string()];
        for i in 2..5 {
            multi_errors.push(format!("error {}", i));
        }
        let multi_error: Validated<String, i32> = Validated::MultiInvalid(multi_errors);

        b.iter(|| {
            let errors1 = black_box(single_error.errors());
            let errors2 = black_box(multi_error.errors());
            (errors1, errors2)
        });
    });

    // Benchmark Validated to_result conversion
    group.bench_function("validated_to_result", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.to_result());
            let result2 = black_box(invalid.to_result());
            (result1, result2)
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

#[cfg(feature = "advanced")]
fn io_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IO Operations");

    // Benchmark IO creation methods
    group.bench_function("io_pure_creation", |b| {
        b.iter(|| black_box(IO::pure(42)));
    });

    group.bench_function("io_new_creation", |b| {
        b.iter(|| black_box(IO::new(|| 42)));
    });

    // Benchmark IO execution
    group.bench_function("io_run", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.run()));
    });

    // Benchmark IO mapping
    group.bench_function("io_fmap", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.fmap(|x| x * 2)));
    });

    // Benchmark IO binding
    group.bench_function("io_bind", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.bind(|x| IO::pure(x * 2))));
    });

    // Benchmark IO chaining operations
    group.bench_function("io_chain", |b| {
        let io = IO::pure(10);
        b.iter(|| {
            black_box(
                io.fmap(|x| x + 5)
                    .bind(|x| IO::pure(x * 2))
                    .fmap(|x| x.to_string()),
            )
        });
    });

    // Benchmark IO with non-trivial computation
    group.bench_function("io_computation", |b| {
        b.iter(|| {
            black_box(IO::new(|| {
                let mut sum = 0;
                for i in 0..100 {
                    sum += i;
                }
                sum
            }))
        });
    });

    // Benchmark IO delay operation (with minimal delay for benchmarking purposes)
    group.bench_function("io_delay_creation", |b| {
        b.iter(|| black_box(IO::delay(std::time::Duration::from_nanos(1), 42)));
    });

    // Benchmark IO try_get
    group.bench_function("io_try_get", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.try_get()));
    });

    // Benchmark IO apply
    group.bench_function("io_apply", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.apply(|x: i32| IO::pure(x * 2))));
    });

    // Benchmark IO with string operations
    group.bench_function("io_string_operations", |b| {
        let s = "Hello, world!".to_string();
        b.iter(|| {
            black_box(
                IO::pure(s.clone())
                    .fmap(|s| s.to_uppercase())
                    .fmap(|s| s + "!"),
            )
        });
    });

    // Benchmark nested IO operations
    group.bench_function("io_nested_operations", |b| {
        b.iter(|| {
            black_box(
                IO::pure(10)
                    .bind(|x| IO::pure(x * 2).bind(|y| IO::pure(y + 5).bind(|z| IO::pure(z * z)))),
            )
        });
    });

    group.finish();
}

fn writer_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Writer Operations");

    // Benchmark creating a simple Writer
    group.bench_function("writer_create", |b| {
        b.iter(|| black_box(Writer::new(Log(vec!["log entry".to_string()]), 42)))
    });

    // Benchmark retrieving value from Writer (should be fast with lazy evaluation)
    group.bench_function("writer_value", |b| {
        let writer = Writer::new(Log(vec!["log entry".to_string()]), 42);
        b.iter(|| black_box(writer.clone().value()))
    });

    // Benchmark log evaluation (where the actual work happens)
    group.bench_function("writer_log", |b| {
        let writer = Writer::new(Log(vec!["log entry".to_string()]), 42);
        b.iter(|| black_box(writer.clone().log()))
    });

    // Benchmark chaining operations with Writer
    group.bench_function("writer_chain_2", |b| {
        let writer = Writer::new(Log(vec!["initial".to_string()]), 5);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x| Writer::new(Log(vec![format!("doubled {} to {}", x, x * 2)]), x * 2)),
            )
        })
    });

    // Benchmark chaining multiple operations (demonstrates lazy evaluation benefit)
    group.bench_function("writer_chain_5", |b| {
        let writer = Writer::new(Log(vec!["initial".to_string()]), 5);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x| Writer::new(Log(vec![format!("step 1: {}", x)]), x + 1))
                    .bind(|x| Writer::new(Log(vec![format!("step 2: {}", x)]), x * 2))
                    .bind(|x| Writer::new(Log(vec![format!("step 3: {}", x)]), x - 3))
                    .bind(|x| Writer::new(Log(vec![format!("step 4: {}", x)]), x * x)),
            )
        });
    });

    // Benchmark a chain that only evaluates the final log at the end
    group.bench_function("writer_chain_run", |b| {
        let writer = Writer::new(Log(vec!["initial".to_string()]), 5);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x| Writer::new(Log(vec![format!("step 1: {}", x)]), x + 1))
                    .bind(|x| Writer::new(Log(vec![format!("step 2: {}", x)]), x * 2))
                    .bind(|x| Writer::new(Log(vec![format!("step 3: {}", x)]), x - 3))
                    .bind(|x| Writer::new(Log(vec![format!("step 4: {}", x)]), x * x))
                    .run(),
            )
        });
    });

    group.finish();
}

fn either_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Either Operations");

    // Benchmark Either creation
    group.bench_function("either_create_left", |b| {
        b.iter(|| black_box(Either::<_, i32>::left("left value".to_string())))
    });

    group.bench_function("either_create_right", |b| {
        b.iter(|| black_box(Either::<String, _>::right(42)))
    });

    // Benchmark functor operations
    group.bench_function("either_fmap", |b| {
        let left: Either<String, i32> = Either::left("error".to_string());
        let right: Either<String, i32> = Either::right(42);

        b.iter(|| {
            let result1 = black_box(left.clone().fmap(|x| x * 2));
            let result2 = black_box(right.clone().fmap(|x| x * 2));
            (result1, result2)
        })
    });

    // Benchmark monad operations
    group.bench_function("either_bind", |b| {
        let left: Either<String, i32> = Either::left("error".to_string());
        let right: Either<String, i32> = Either::right(42);

        b.iter(|| {
            let result1 = black_box(left.clone().bind(|x| Either::<String, _>::right(x * 2)));
            let result2 = black_box(right.clone().bind(|x| Either::<String, _>::right(x * 2)));
            (result1, result2)
        })
    });

    // Benchmark pattern matching
    group.bench_function("either_pattern_match", |b| {
        let left: Either<String, i32> = Either::left("error".to_string());
        let right: Either<String, i32> = Either::right(42);

        b.iter(|| {
            let result1 = black_box(match left.clone() {
                Either::Left(s) => s,
                Either::Right(_) => "default".to_string(),
            });
            let result2 = black_box(match right.clone() {
                Either::Left(_) => 0,
                Either::Right(n) => n,
            });
            (result1, result2)
        })
    });

    // Benchmark map_left and map_right
    group.bench_function("either_map_left_right", |b| {
        let left: Either<i32, String> = Either::left(42);
        let right: Either<i32, String> = Either::right("hello".to_string());

        b.iter(|| {
            let result1 = black_box(left.clone().map_left(|x| x * 2));
            let result2 = black_box(right.clone().map_right(|s| s.to_uppercase()));
            (result1, result2)
        })
    });

    group.finish();
}

fn wrapper_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Wrapper Types Operations");

    // Sum and Product
    group.bench_function("wrapper_sum_product", |b| {
        b.iter(|| {
            // Sum operations
            let sum1 = black_box(Sum(5));
            let sum2 = black_box(Sum(10));
            let sum_result = black_box(sum1.clone().combine_owned(sum2.clone()));

            // Product operations
            let prod1 = black_box(Product(5));
            let prod2 = black_box(Product(10));
            let prod_result = black_box(prod1.clone().combine_owned(prod2.clone()));

            (sum_result, prod_result)
        })
    });

    // Min and Max
    group.bench_function("wrapper_min_max", |b| {
        b.iter(|| {
            // Min operations
            let min1 = black_box(Min(5));
            let min2 = black_box(Min(10));
            let min_result = black_box(min1.clone().combine_owned(min2.clone()));

            // Max operations
            let max1 = black_box(Max(5));
            let max2 = black_box(Max(10));
            let max_result = black_box(max1.clone().combine_owned(max2.clone()));

            (min_result, max_result)
        })
    });

    // First and Last
    group.bench_function("wrapper_first_last", |b| {
        b.iter(|| {
            // First operations
            let first1 = black_box(First(Some(5)));
            let first2 = black_box(First(Some(10)));
            let first_none = black_box(First(None));
            let first_result1 = black_box(first1.clone().combine_owned(first2.clone()));
            let first_result2 = black_box(first1.clone().combine_owned(first_none.clone()));

            // Last operations
            let last1 = black_box(Last(Some(5)));
            let last2 = black_box(Last(Some(10)));
            let last_none = black_box(Last(None));
            let last_result1 = black_box(last1.clone().combine_owned(last2.clone()));
            let last_result2 = black_box(last1.clone().combine_owned(last_none.clone()));

            (first_result1, first_result2, last_result1, last_result2)
        })
    });

    // Thunk and Value
    group.bench_function("wrapper_thunk_value", |b| {
        b.iter(|| {
            // Thunk operations
            let thunk = black_box(Thunk::new(|| 42));
            let thunk_result = black_box(thunk.evaluate());

            // Value operations
            let value = black_box(Value(42));
            let value_result = black_box(value.evaluate());

            (thunk_result, value_result)
        })
    });

    // BoxedFn
    group.bench_function("wrapper_boxed_fn", |b| {
        b.iter(|| {
            // BoxedFn operations
            let boxed_fn = black_box(BoxedFn(Box::new(|| 21 * 2)));
            let boxed_fn_result = black_box(boxed_fn.evaluate());

            boxed_fn_result
        })
    });

    group.finish();
}

fn lens_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Lens Operations");

    // Define a simple struct for lens testing
    #[derive(Clone)]
    struct Person {
        name: String,
        age: i32,
    }

    // Create lens for the name field
    let name_lens = Lens::new(
        |p: &Person| p.name.clone(),
        |p: Person, name: String| {
            let mut new_p = p;
            new_p.name = name;
            new_p
        },
    );

    // Create lens for the age field
    let age_lens = Lens::new(
        |p: &Person| p.age,
        |p: Person, age: i32| {
            let mut new_p = p;
            new_p.age = age;
            new_p
        },
    );

    // Benchmark lens view operation
    group.bench_function("lens_view", |b| {
        let person = Person {
            name: "John".to_string(),
            age: 30,
        };

        b.iter(|| {
            let name = black_box(name_lens.get(&person));
            let age = black_box(age_lens.get(&person));
            (name, age)
        })
    });

    // Benchmark lens set operation
    group.bench_function("lens_set", |b| {
        let person = Person {
            name: "John".to_string(),
            age: 30,
        };

        b.iter(|| {
            let new_person1 = black_box(name_lens.set(person.clone(), "Jane".to_string()));
            let new_person2 = black_box(age_lens.set(person.clone(), 31));
            (new_person1, new_person2)
        })
    });

    // Benchmark lens modify operation
    group.bench_function("lens_modify", |b| {
        let person = Person {
            name: "John".to_string(),
            age: 30,
        };

        b.iter(|| {
            let new_person1 = black_box(name_lens.modify(person.clone(), |name| name + " Doe"));
            let new_person2 = black_box(age_lens.modify(person.clone(), |age| age + 1));
            (new_person1, new_person2)
        })
    });

    group.finish();
}

fn prism_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Prism Operations");

    // Define a simple enum for prism testing
    #[derive(Clone, Debug, PartialEq)]
    enum Shape {
        Circle(f64),             // radius
        Rectangle(f64, f64),     // width, height
        Triangle(f64, f64, f64), // a, b, c sides
    }

    // Create a prism for the Circle variant
    let circle_prism = Prism::new(
        |shape: &Shape| match shape {
            Shape::Circle(radius) => Some(*radius),
            _ => None,
        },
        |radius: &f64| Shape::Circle(*radius),
    );

    // Create a prism for the Rectangle variant
    let rectangle_prism = Prism::new(
        |shape: &Shape| match shape {
            Shape::Rectangle(w, h) => Some((*w, *h)),
            _ => None,
        },
        |dims: &(f64, f64)| Shape::Rectangle(dims.0, dims.1),
    );

    // Benchmark prism preview operation
    group.bench_function("prism_preview", |b| {
        let circle = Shape::Circle(5.0);
        let rectangle = Shape::Rectangle(10.0, 20.0);
        let triangle = Shape::Triangle(3.0, 4.0, 5.0);

        b.iter(|| {
            let circle_radius = black_box(circle_prism.preview(&circle));
            let rect_dims = black_box(rectangle_prism.preview(&rectangle));
            let no_match = black_box(circle_prism.preview(&triangle));
            (circle_radius, rect_dims, no_match)
        })
    });

    // Benchmark prism review operation
    group.bench_function("prism_review", |b| {
        // Create values outside of the benchmark to avoid measuring allocation
        let radius = 7.0;
        let rectangle_dims = (15.0, 25.0);

        b.iter(|| {
            let new_circle = black_box(circle_prism.review(&radius));
            let new_rectangle = black_box(rectangle_prism.review(&rectangle_dims));
            (new_circle, new_rectangle)
        })
    });

    group.finish();
}

fn reader_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Reader Operations");

    // Define a simple environment
    #[derive(Clone)]
    struct Config {
        multiplier: i32,
        prefix: String,
    }

    // Benchmark Reader creation and execution
    group.bench_function("reader_create_run", |b| {
        b.iter(|| {
            let config = Config {
                multiplier: 10,
                prefix: "value: ".to_string(),
            };

            let reader1 = black_box(Reader::new(|cfg: Config| cfg.multiplier * 5));
            let reader2 = black_box(Reader::new(|cfg: Config| cfg.prefix + "hello"));

            let result1 = black_box(reader1.run_reader(config.clone()));
            let result2 = black_box(reader2.run_reader(config));

            (result1, result2)
        })
    });

    // Benchmark Reader functor operations
    group.bench_function("reader_functor", |b| {
        b.iter(|| {
            let config = Config {
                multiplier: 10,
                prefix: "value: ".to_string(),
            };
            let reader = Reader::new(|cfg: Config| cfg.multiplier);

            let mapped = black_box(reader.fmap(|x| x * 2));
            let result = black_box(mapped.run_reader(config));
            result
        })
    });

    // Benchmark Reader applicative operations
    group.bench_function("reader_applicative", |b| {
        b.iter(|| {
            let config = Config {
                multiplier: 10,
                prefix: "value: ".to_string(),
            };
            let reader1 = Reader::new(|cfg: Config| cfg.multiplier);
            let reader2 = Reader::new(|cfg: Config| cfg.multiplier + 5);

            let result = black_box(reader1.combine(&reader2, |x, y| x + y).run_reader(config));
            result
        })
    });

    // Benchmark Reader monad operations
    group.bench_function("reader_monad", |b| {
        b.iter(|| {
            let config = Config {
                multiplier: 10,
                prefix: "value: ".to_string(),
            };
            let reader = Reader::new(|cfg: Config| cfg.multiplier);

            let chained = black_box(
                reader.bind(|x| Reader::new(move |cfg: Config| format!("{}{}", cfg.prefix, x))),
            );
            let result = black_box(chained.run_reader(config));
            result
        })
    });

    // Benchmark Reader ask operation
    group.bench_function("reader_ask", |b| {
        b.iter(|| {
            let config = Config {
                multiplier: 10,
                prefix: "value: ".to_string(),
            };
            let reader = black_box(Reader::<Config, i32>::ask().fmap(|cfg| cfg.multiplier * 2));
            let result = black_box(reader.run_reader(config));
            result
        })
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
    writer_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    async_monad_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(not(feature = "async"))]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
    io_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

#[cfg(feature = "async")]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    writer_benchmarks,
    async_monad_benchmarks,
    cont_benchmarks,
    state_benchmarks,
    choice_benchmarks,
    io_benchmarks,
    either_benchmarks,
    wrapper_benchmarks,
    lens_benchmarks,
    prism_benchmarks,
    reader_benchmarks,
);

criterion_main!(datatype_benches);
