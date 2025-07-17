use criterion::Criterion;
use rustica::datatypes::reader::Reader;
use std::hint::black_box;

// Mock environment and functions for benchmarking
#[derive(Clone, PartialEq, Eq, Debug)]
struct Config {
    pub setting: String,
}

fn get_setting(config: &Config) -> String {
    config.setting.clone()
}

fn process_data(data: i32) -> Reader<Config, String> {
    Reader::new(move |config: Config| format!("Processing {data} with {0}", config.setting))
}

pub fn reader_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Reader");
    let initial_config = Config {
        setting: "initial".to_string(),
    };

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(Reader::new(|config: Config| config.setting.len()));
        });
    });

    group.bench_function("functor_ops", |b| {
        let reader: Reader<Config, usize> = Reader::new(|config: Config| config.setting.len());
        b.iter(|| {
            black_box(
                reader
                    .clone()
                    .fmap(|len| len * 2)
                    .run_reader(initial_config.clone()),
            );
        });
    });

    group.bench_function("applicative_ops", |b| {
        let reader_a: Reader<Config, i32> = Reader::new(|_: Config| 10);
        b.iter(|| {
            let reader_b: Reader<Config, i32> = Reader::new(|_: Config| 20);
            // pure
            black_box(Reader::new(|_: Config| 42).run_reader(initial_config.clone()));
            // lift2
            let lift2_equiv = reader_a
                .clone()
                .bind(move |a| reader_b.clone().fmap(move |b| a + b));
            black_box(lift2_equiv.run_reader(initial_config.clone()));
        });
    });

    group.bench_function("monad_ops", |b| {
        let reader: Reader<Config, i32> = Reader::new(|_: Config| 100);
        b.iter(|| {
            black_box(
                reader
                    .clone()
                    .bind(process_data)
                    .run_reader(initial_config.clone()),
            );
        });
    });

    group.bench_function("special_ops", |b| {
        let reader: Reader<Config, String> = Reader::new(|c: Config| get_setting(&c));
        b.iter(|| {
            let modified_config = Config {
                setting: "modified".to_string(),
            };
            black_box(Reader::<Config, Config>::ask().run_reader(initial_config.clone()));
            black_box(
                reader
                    .clone()
                    .local(move |_| modified_config.clone())
                    .run_reader(initial_config.clone()),
            );
        });
    });

    group.finish();
}
