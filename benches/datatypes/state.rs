#[cfg(feature = "advanced")]
use criterion::{black_box, Criterion};
#[cfg(feature = "advanced")]
use rustica::datatypes::state::State;
#[cfg(feature = "advanced")]
use rustica::datatypes::state::{get, modify, put};
#[cfg(feature = "advanced")]
use std::time::SystemTime;

// Define types for benchmarks
#[cfg(feature = "advanced")]
#[derive(Clone, Debug)]
struct LogEntry {
    #[allow(dead_code)]
    timestamp: u64,
    #[allow(dead_code)]
    level: String,
    #[allow(dead_code)]
    message: String,
}

#[cfg(feature = "advanced")]
#[derive(Clone, Debug)]
struct FileReaderState {
    #[allow(dead_code)]
    buffer: String,
    #[allow(dead_code)]
    position: usize,
    #[allow(dead_code)]
    last_read_time: SystemTime,
    logs: Vec<LogEntry>,
}

#[cfg(feature = "advanced")]
impl Default for FileReaderState {
    fn default() -> Self {
        FileReaderState {
            buffer: String::new(),
            position: 0,
            last_read_time: SystemTime::now(),
            logs: Vec::new(),
        }
    }
}

#[cfg(feature = "advanced")]
pub fn state_benchmarks(c: &mut Criterion) {
    // Basic operations
    let mut group = c.benchmark_group("State - Basic Operations");

    group.bench_function("create_and_run", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(5))
        });
    });

    group.bench_function("pure", |b| {
        b.iter(|| {
            let state = State::pure(42);
            black_box(state.run_state(1))
        });
    });

    group.bench_function("run_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.run_state(10))
        });
    });

    group.finish();

    // Core operations
    let mut group = c.benchmark_group("State - Core Operations");

    group.bench_function("eval_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.eval_state(10))
        });
    });

    group.bench_function("exec_state", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s * 2, s + 1));
            black_box(state.exec_state(10))
        });
    });

    group.bench_function("get", |b| {
        b.iter(|| {
            let state = get::<i32>();
            black_box(state.run_state(10))
        });
    });

    group.bench_function("put", |b| {
        b.iter(|| {
            let state = put(42);
            black_box(state.run_state(10))
        });
    });

    group.bench_function("modify", |b| {
        b.iter(|| {
            let state = modify(|s: i32| s * 2);
            black_box(state.run_state(10))
        });
    });

    group.finish();

    // Functor operations
    let mut group = c.benchmark_group("State - Functor Operations");

    group.bench_function("fmap_simple", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s, s + 1));
            black_box(state.fmap(|x: i32| x * 2))
        });
    });

    group.bench_function("fmap_chain", |b| {
        b.iter(|| {
            let state = State::new(|s: i32| (s, s + 1));
            black_box(state.fmap(|x: i32| x * 2).fmap(|x: i32| x + 1))
        });
    });

    group.finish();

    // Monad operations
    let mut group = c.benchmark_group("State - Monad Operations");

    group.bench_function("bind_simple", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            black_box(state.bind(|x: i32| State::pure(x * 2)))
        });
    });

    group.bench_function("bind_chain", |b| {
        b.iter(|| {
            let state: State<i32, i32> = State::pure(42);
            black_box(
                state
                    .bind(|x: i32| State::pure(x * 2))
                    .bind(|x: i32| State::pure(x + 10)),
            )
        });
    });

    group.finish();

    // Chain operations
    let mut group = c.benchmark_group("State - Chain Operations");

    group.bench_function("get_put_chain", |b| {
        b.iter(|| {
            black_box(
                get::<i32>()
                    .bind(|s: i32| put(s * 2))
                    .bind(|_: ()| get::<i32>()),
            )
        });
    });

    group.bench_function("chain_with_statechange", |b| {
        b.iter(|| {
            let result = get::<i32>().bind(|s: i32| {
                let value = s;
                modify(move |state: i32| state + value).bind(move |_: ()| State::pure(value * 2))
            });

            black_box(result.run_state(5))
        });
    });

    group.finish();

    // Real-world use cases
    let mut group = c.benchmark_group("State - Real World");

    group.bench_function("document_processing", |b| {
        #[derive(Clone, Debug)]
        struct Document {
            content: String,
            processed: bool,
            approved: bool,
        }

        fn process_content() -> State<Document, ()> {
            State::new(|mut doc: Document| {
                doc.content = doc.content.to_uppercase();
                doc.processed = true;
                ((), doc)
            })
        }

        fn approve_document() -> State<Document, bool> {
            State::new(|mut doc: Document| {
                doc.approved = doc.processed;
                (doc.approved, doc)
            })
        }

        b.iter(|| {
            let doc = Document {
                content: "draft document".to_string(),
                processed: false,
                approved: false,
            };

            let pipeline = process_content().bind(|_| approve_document());
            black_box(pipeline.run_state(doc))
        });
    });

    group.bench_function("logging_system", |b| {
        b.iter(|| {
            fn append_log(
                level: &'static str,
                message: &'static str,
            ) -> State<FileReaderState, ()> {
                let entry = LogEntry {
                    timestamp: 1647271234,
                    level: level.to_string(),
                    message: message.to_string(),
                };

                State::new(move |mut state: FileReaderState| {
                    state.logs.push(entry.clone());
                    ((), state)
                })
            }

            let log_operations = append_log("INFO", "Application started")
                .bind(|_| append_log("DEBUG", "Loading configuration"))
                .bind(|_| append_log("ERROR", "Failed to connect"));

            black_box(log_operations.run_state(FileReaderState::default()))
        });
    });

    group.finish();
}

#[cfg(not(feature = "advanced"))]
pub fn state_benchmarks(_c: &mut Criterion) {
    // No-op when feature is disabled
}
