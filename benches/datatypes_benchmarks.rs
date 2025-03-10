use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rustica::datatypes::maybe::Maybe;
use rustica::datatypes::id::Id;
use rustica::datatypes::validated::Validated;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use smallvec::smallvec;

#[cfg(feature = "advanced")] 
use rustica::datatypes::writer::Writer;

#[cfg(feature = "advanced")] 
use rustica::datatypes::reader::Reader;

#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "async")]
use tokio::runtime::Runtime;
#[cfg(feature = "async")]
use std::sync::Arc;

fn maybe_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Maybe Operations");
    
    // Benchmark Maybe::map with reference vs ownership methods
    group.bench_function("maybe_map_ref", |b| {
        let maybe = Maybe::Just(10);
        b.iter(|| {
            black_box(maybe.fmap(|x| x * 2))
        });
    });
    
    group.bench_function("maybe_map_owned", |b| {
        b.iter(|| {
            black_box(Maybe::Just(10).fmap_owned(|x| x * 2))
        });
    });
    
    // Benchmark Maybe chaining operations
    group.bench_function("maybe_chain", |b| {
        let maybe = Maybe::Just(10);
        b.iter(|| {
            black_box(
                maybe.fmap(|x| x + 5)
                    .bind(|x| if *x > 10 { Maybe::Just(x * 2) } else { Maybe::Nothing })
                    .fmap(|x| x.to_string())
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
        b.iter(|| {
            black_box(id.fmap(|x| x * 2))
        });
    });
    
    group.bench_function("id_map_owned", |b| {
        b.iter(|| {
            black_box(Id::new(10).fmap_owned(|x| x * 2))
        });
    });
    
    // Benchmark Id chaining operations
    group.bench_function("id_chain", |b| {
        let id = Id::new(10);
        b.iter(|| {
            black_box(
                id.fmap(|x| x + 5)
                  .bind(|x| Id::new(*x * 2))
                  .fmap(|x| x.to_string())
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
                },
                (v@Validated::Valid(_), _) => v,
                (_, v@Validated::Valid(_)) => v,
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
        b.iter(|| {
            black_box(AsyncM::pure(10))
        });
    });
    
    group.bench_function("asyncm_new_creation", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async { 10 }))
        });
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
            let bound = async_value.clone().bind(|x| async move { 
                AsyncM::pure(x + 5) 
            });
            black_box(bound)
        });
    });
    
    // Benchmark AsyncM execution performance for a simple value
    group.bench_function("asyncm_execute_pure", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| {
            rt.block_on(async {
                black_box(async_value.clone().try_get().await)
            })
        });
    });
    
    // Benchmark AsyncM execution performance for a more complex chain
    group.bench_function("asyncm_execute_chain", |b| {
        let async_value = AsyncM::pure(10);
        b.iter(|| {
            rt.block_on(async {
                let result = async_value.clone()
                    .fmap(|x| async move { x + 5 })
                    .bind(|x| async move { AsyncM::pure(x * 2) })
                    .bind(|x| async move { AsyncM::pure(x - 1) })
                    .try_get().await;
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
                0
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

#[cfg(not(feature = "async"))]
fn async_monad_benchmarks(_: &mut Criterion) {
    // Empty implementation when async feature is not enabled
}

#[cfg(feature = "advanced")]
fn reader_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Reader Operations");
    
    // Simple environment for testing
    #[derive(Clone)]
    struct TestEnv {
        value: i32,
        multiplier: i32,
    }
    
    // Benchmark Reader creation
    group.bench_function("reader_new", |b| {
        b.iter(|| {
            black_box(Reader::new(|env: TestEnv| env.value * env.multiplier))
        });
    });
    
    // Benchmark Reader::ask (getting the environment)
    group.bench_function("reader_ask", |b| {
        b.iter(|| {
            black_box(Reader::<TestEnv, TestEnv>::ask())
        });
    });
    
    // Benchmark Reader::asks (transforming the environment)
    group.bench_function("reader_asks", |b| {
        b.iter(|| {
            black_box(Reader::<TestEnv, i32>::asks(|env| env.value))
        });
    });
    
    // Benchmark Reader::fmap (mapping over results)
    group.bench_function("reader_fmap", |b| {
        let reader = Reader::new(|env: TestEnv| env.value);
        b.iter(|| {
            black_box(reader.fmap(|x| x.to_string()))
        });
    });
    
    // Benchmark Reader::bind (chaining readers)
    group.bench_function("reader_bind", |b| {
        let reader = Reader::new(|env: TestEnv| env.value);
        b.iter(|| {
            black_box(reader.bind(|value| {
                Reader::new(move |env: TestEnv| value * env.multiplier)
            }))
        });
    });
    
    // Benchmark Reader::local (modifying the environment)
    group.bench_function("reader_local", |b| {
        let reader = Reader::new(|env: TestEnv| env.value * env.multiplier);
        b.iter(|| {
            black_box(reader.local(|mut env| {
                env.multiplier *= 2;
                env
            }))
        });
    });
    
    // Benchmark Reader::combine (combining two readers)
    group.bench_function("reader_combine", |b| {
        let reader1 = Reader::new(|env: TestEnv| env.value);
        let reader2 = Reader::new(|env: TestEnv| env.multiplier);
        b.iter(|| {
            black_box(reader1.combine(&reader2, |v, m| v * m))
        });
    });
    
    // Benchmark execution performance of a complex reader chain
    group.bench_function("reader_complex_chain", |b| {
        let env = TestEnv { value: 10, multiplier: 5 };
        let reader = Reader::new(|e: TestEnv| e.value)
            .bind(|val| {
                Reader::new(move |e: TestEnv| val + e.multiplier)
            })
            .fmap(|val| val * 2)
            .local(|mut e| {
                e.multiplier += 3;
                e
            });
        
        b.iter(|| {
            black_box(reader.run_reader(env.clone()))
        });
    });
    
    group.finish();
}

#[cfg(feature = "advanced")]
fn writer_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Writer Operations");
    
    // Define a simple log type for testing
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
    
    // Benchmark Writer creation
    group.bench_function("writer_new", |b| {
        b.iter(|| {
            black_box(Writer::new(
                Log(vec!["Created value".to_string()]), 
                42
            ))
        });
    });
    
    // Benchmark Writer::tell (creating a Writer with just a log)
    group.bench_function("writer_tell", |b| {
        b.iter(|| {
            black_box(Writer::<Log, ()>::tell(
                Log(vec!["Log message".to_string()])
            ))
        });
    });
    
    // Benchmark Writer::run (extracting value and log)
    group.bench_function("writer_run", |b| {
        let writer = Writer::new(Log(vec!["Log message".to_string()]), 42);
        b.iter(|| {
            black_box(writer.clone().run())
        });
    });
    
    // Benchmark Writer::fmap (mapping over the value)
    group.bench_function("writer_fmap", |b| {
        let writer = Writer::new(Log(vec!["Computed value".to_string()]), 42);
        b.iter(|| {
            black_box(writer.fmap(|x| x * 2))
        });
    });
    
    // Benchmark Writer::bind (chaining Writers)
    group.bench_function("writer_bind", |b| {
        let writer = Writer::new(Log(vec!["First log".to_string()]), 42);
        b.iter(|| {
            black_box(writer.bind(|value| {
                Writer::new(
                    Log(vec![format!("Processed value: {}", value)]), 
                    value * 2
                )
            }))
        });
    });
    
    // Benchmark complex chaining of Writer operations
    group.bench_function("writer_complex_chain", |b| {
        let writer = Writer::new(Log(vec!["Initial log".to_string()]), 10);
        b.iter(|| {
            black_box(
                writer.clone()
                    .fmap(|x| x * 2)
                    .bind(|value| {
                        Writer::new(
                            Log(vec![format!("Doubled: {}", value)]), 
                            value + 5
                        )
                    })
                    .bind(|value| {
                        Writer::new(
                            Log(vec![format!("Added 5: {}", value)]), 
                            value.to_string()
                        )
                    })
                    .run()
            )
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
    validated_benchmarks
);

#[cfg(not(feature = "async"))]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    reader_benchmarks,
    writer_benchmarks
);

#[cfg(feature = "async")]
#[cfg(not(feature = "advanced"))]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    async_monad_benchmarks
);

#[cfg(feature = "async")]
#[cfg(feature = "advanced")]
criterion_group!(
    datatype_benches,
    maybe_benchmarks,
    id_benchmarks,
    validated_benchmarks,
    reader_benchmarks,
    writer_benchmarks,
    async_monad_benchmarks
);

criterion_main!(datatype_benches);
