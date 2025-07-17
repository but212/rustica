use criterion::Criterion;
use rustica::datatypes::writer::Writer;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use std::hint::black_box;

fn process_data(data: i32) -> Writer<String, String> {
    Writer::new(
        format!("Processed data: {data}. "),
        format!("Processed {data}"),
    )
}

pub fn writer_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Writer");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(Writer::new("Initial. ".to_string(), 1));
        });
    });

    group.bench_function("functor_ops", |b| {
        let writer = Writer::new("Initial. ".to_string(), 1);
        b.iter(|| {
            black_box(writer.clone().fmap(|x| x + 1));
        });
    });

    group.bench_function("monad_ops", |b| {
        let writer = Writer::new("Initial. ".to_string(), 1);
        b.iter(|| {
            black_box(writer.clone().bind(|x| process_data(*x)));
        });
    });

    group.bench_function("special_ops", |b| {
        b.iter(|| {
            black_box(Writer::<String, ()>::tell("Log this.".to_string()));
        });
    });

    group.finish();
}
