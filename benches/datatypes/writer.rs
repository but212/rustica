use criterion::{black_box, Criterion};
use rustica::datatypes::writer::Writer;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::pure::Pure;
use rustica::traits::semigroup::Semigroup;

// A log type for benchmarking Writer performance
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Log {
    _entries: Vec<String>,
}

impl Semigroup for Log {
    fn combine(&self, other: &Self) -> Self {
        let mut entries = self._entries.clone();
        entries.extend(other._entries.clone());
        Log { _entries: entries }
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut entries = self._entries;
        entries.extend(other._entries);
        Log { _entries: entries }
    }
}

impl Monoid for Log {
    fn empty() -> Self {
        Log {
            _entries: Vec::new(),
        }
    }
}

// A different log type with a more compact representation
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CountLog {
    count: usize,
    message: String,
}

impl Semigroup for CountLog {
    fn combine(&self, other: &Self) -> Self {
        CountLog {
            count: self.count + other.count,
            message: format!("{} & {}", self.message, other.message),
        }
    }

    fn combine_owned(self, other: Self) -> Self {
        CountLog {
            count: self.count + other.count,
            message: format!("{} & {}", self.message, other.message),
        }
    }
}

impl Monoid for CountLog {
    fn empty() -> Self {
        CountLog {
            count: 0,
            message: String::new(),
        }
    }
}

pub fn writer_benchmarks(c: &mut Criterion) {
    // Basic operations benchmark group
    let mut group = c.benchmark_group("Writer - Basic Operations");

    // Creation benchmarks
    group.bench_function("new with empty log", |b| {
        b.iter(|| black_box(Writer::<Log, i32>::new(Log::empty(), 42)));
    });

    group.bench_function("new with non-empty log", |b| {
        let log = Log {
            _entries: vec!["Entry 1".to_string(), "Entry 2".to_string()],
        };
        b.iter(|| {
            let writer = Writer::<Log, i32>::new(log.clone(), 42);
            black_box(writer)
        });
    });

    group.bench_function("pure", |b| {
        b.iter(|| black_box(Writer::<Log, i32>::pure(&42)));
    });

    group.bench_function("tell", |b| {
        let log = Log {
            _entries: vec!["log entry".to_string()],
        };
        b.iter(|| {
            let log = log.clone();
            black_box(Writer::<Log, ()>::tell(log))
        });
    });

    // Access benchmarks
    group.bench_function("value extraction", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            // No need to clone since value() consumes the writer but doesn't use the log
            let writer_clone = writer.clone();
            black_box(writer_clone.value())
        });
    });

    group.bench_function("log extraction", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        let writer_clone = writer.clone();
        b.iter(|| black_box(writer_clone.clone().log()));
    });

    group.bench_function("run", |b| {
        let log = Log::empty();
        let writer = Writer::<Log, i32>::new(log, 42);
        b.iter(|| black_box(writer.clone().run()));
    });

    // CountLog variant
    group.bench_function("CountLog operations", |b| {
        let log = CountLog {
            count: 5,
            message: "Initial log".to_string(),
        };
        let writer = Writer::<CountLog, i32>::new(log.clone(), 42);
        b.iter(|| black_box(writer.clone().log()));
    });

    group.finish();

    // Functor operations
    let mut group = c.benchmark_group("Writer - Functor Operations");

    group.bench_function("fmap", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| black_box(writer.clone().fmap(|x| x + 1)));
    });

    group.bench_function("fmap complex", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(writer.clone().fmap(|x: &i32| {
                let mut result = 0;
                for i in 0..*x {
                    result += i;
                }
                result
            }))
        });
    });

    group.bench_function("fmap chained", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .fmap(|x: &i32| x + 10)
                    .fmap(|x: &i32| x * 2)
                    .fmap(|x: &i32| x - 5),
            )
        });
    });

    group.finish();

    // Applicative operations
    let mut group = c.benchmark_group("Writer - Applicative Operations");

    group.bench_function("apply", |b| {
        let writer_fn = Writer::<Log, fn(&i32) -> i32>::new(Log::empty(), |x: &i32| x + 1);
        let writer_val = Writer::<Log, i32>::new(Log::empty(), 42);
        b.iter_batched_ref(
            || (writer_val.clone(), writer_fn.clone()),
            |(val, func)| black_box(val.apply(func)),
            criterion::BatchSize::SmallInput,
        );
    });

    group.bench_function("lift2", |b| {
        b.iter_batched_ref(
            || {
                (
                    Writer::<Log, i32>::new(Log::empty(), 42),
                    Writer::<Log, i32>::new(Log::empty(), 10),
                )
            },
            |(w1, w2)| black_box(w1.lift2(w2, |x: &i32, y: &i32| x + y)),
            criterion::BatchSize::SmallInput,
        );
    });

    group.bench_function("lift3", |b| {
        b.iter_batched_ref(
            || {
                (
                    Writer::<Log, i32>::new(Log::empty(), 42),
                    Writer::<Log, i32>::new(Log::empty(), 10),
                    Writer::<Log, i32>::new(Log::empty(), 5),
                )
            },
            |(w1, w2, w3)| black_box(w1.lift3(w2, w3, |x: &i32, y: &i32, z: &i32| x + y + z)),
            criterion::BatchSize::SmallInput,
        );
    });

    group.finish();

    // Monad operations
    let mut group = c.benchmark_group("Writer - Monad Operations");

    group.bench_function("bind simple", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        let target_fn = |x: &i32| Writer::<Log, i32>::new(Log::empty(), x + 1);
        b.iter(|| black_box(writer.clone().bind(target_fn)));
    });

    group.bench_function("bind with logging", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        let bind_fn = |x: &i32| {
            let log = Log {
                _entries: vec![format!("Processed value: {}", x)],
            };
            Writer::<Log, i32>::new(log, x + 1)
        };

        b.iter(|| black_box(writer.clone().bind(bind_fn)));
    });

    group.bench_function("bind chained", |b| {
        let writer = Writer::<Log, i32>::new(Log::empty(), 42);
        let log1 = Log {
            _entries: vec!["First operation".to_string()],
        };
        let log2 = Log {
            _entries: vec!["Second operation".to_string()],
        };

        b.iter(|| {
            black_box(
                writer
                    .clone()
                    .bind(|x: &i32| Writer::<Log, i32>::new(log1.clone(), x + 10))
                    .bind(|x: &i32| Writer::<Log, i32>::new(log2.clone(), x * 2)),
            )
        });
    });

    group.finish();

    // Real-world use cases
    let mut group = c.benchmark_group("Writer - Use Cases");

    group.bench_function("computation pipeline", |b| {
        b.iter(|| {
            let initial = Writer::<Log, i32>::new(
                Log {
                    _entries: vec!["Starting computation".to_string()],
                },
                10,
            );

            black_box(initial.fmap(|x| x * 2).bind(|x| {
                let log = Log {
                    _entries: vec![format!("Processing value: {}", x)],
                };
                Writer::<Log, i32>::new(log, x + 5)
            }))
        });
    });

    group.bench_function("system config with audit", |b| {
        b.iter(|| {
            #[derive(Clone)]
            struct SystemConfig {
                max_connections: usize,
                debug_mode: bool,
            }

            let initial_config = SystemConfig {
                max_connections: 100,
                debug_mode: false,
            };

            let initial_writer = Writer::<Log, SystemConfig>::new(
                Log {
                    _entries: vec!["Initial configuration loaded".to_string()],
                },
                initial_config,
            );

            black_box(
                initial_writer
                    .bind(|config| {
                        let mut new_config = config.clone();
                        new_config.max_connections = 150;
                        let log = Log {
                            _entries: vec![format!(
                                "Max connections: {} -> {}",
                                config.max_connections, new_config.max_connections
                            )],
                        };
                        Writer::<Log, SystemConfig>::new(log, new_config)
                    })
                    .bind(|config| {
                        let mut new_config = config.clone();
                        new_config.debug_mode = true;
                        let log = Log {
                            _entries: vec!["Debug mode enabled".to_string()],
                        };
                        Writer::<Log, SystemConfig>::new(log, new_config)
                    }),
            )
        });
    });

    group.finish();
}
