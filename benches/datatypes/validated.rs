use criterion::{BenchmarkId, Criterion};
use rustica::datatypes::validated::Validated;
use rustica::traits::functor::Functor;
use std::hint::black_box;

pub fn validated_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Validated");

    // Four errors fit inline; five require heap storage.
    for error_count in [4, 5] {
        group.bench_with_input(
            BenchmarkId::new("invalid_many", error_count),
            &error_count,
            |b, &error_count| {
                let errors: Vec<_> = (0..error_count)
                    .map(|index| format!("error_{index}"))
                    .collect();
                b.iter(|| black_box(Validated::<String, i32>::invalid_many(errors.clone())));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("combine_errors", error_count),
            &error_count,
            |b, &error_count| {
                let left = Validated::<String, i32>::invalid("left".to_string());
                let right = Validated::<String, i32>::invalid_many(
                    (0..error_count).map(|index| format!("error_{index}")),
                );
                b.iter(|| black_box(left.combine_errors(&right)));
            },
        );
    }

    group.bench_function("validated_map", |b| {
        b.iter(|| {
            let value = Validated::<String, i32>::valid(42);
            black_box(value.fmap(|value| value + 1))
        });
    });

    group.bench_function("result_map", |b| {
        b.iter(|| {
            let value = Result::<i32, String>::Ok(42);
            black_box(value.map(|value| value + 1))
        });
    });

    group.finish();
}
