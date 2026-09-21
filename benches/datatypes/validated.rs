use crate::harness::Harness;
use rustica::datatypes::validated::Validated;
use rustica::traits::functor::Functor;
use std::hint::black_box;

pub fn validated_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Validated");

    // Four errors fit inline; five require heap storage.
    for error_count in [4, 5] {
        let name = format!("invalid_many/{error_count}");
        group.bench_batched(
            &name,
            || {
                (0..error_count)
                    .map(|index| format!("error_{index}"))
                    .collect::<Vec<_>>()
            },
            |errors| {
                black_box(Validated::<i32, String>::invalid_many(std::mem::take(
                    errors,
                )));
            },
        );

        let name = format!("combine_errors/{error_count}");
        group.bench_batched(
            &name,
            || {
                let left = Validated::<i32, String>::invalid("left".to_string());
                let right = Validated::<i32, String>::invalid_many(
                    (0..error_count).map(|index| format!("error_{index}")),
                );
                (left, right)
            },
            |(left, right)| {
                black_box(left.clone().combine_errors(right.clone()));
            },
        );
    }

    group.bench_fn("validated_map", || {
        let value = Validated::<i32, String>::valid(42);
        black_box(value.fmap(|value| value + 1));
    });

    group.bench_fn("result_map", || {
        let value = Result::<i32, String>::Ok(42);
        let _ = black_box(value.map(|value| value + 1));
    });

    // Benchmark sequence single-pass performance (happy path and error path)
    for size in [10, 100] {
        let name_valid = format!("sequence_valid/{size}");
        group.bench_batched(
            &name_valid,
            || {
                (0..size)
                    .map(Validated::<i32, String>::valid)
                    .collect::<Vec<_>>()
            },
            |values| {
                black_box(Validated::sequence(std::mem::take(values), |items| {
                    items.iter().sum::<i32>()
                }));
            },
        );

        let name_errors = format!("sequence_mixed/{size}");
        group.bench_batched(
            &name_errors,
            || {
                (0..size)
                    .map(|i| {
                        if i % 2 == 0 {
                            Validated::valid(i)
                        } else {
                            Validated::invalid(format!("err_{i}"))
                        }
                    })
                    .collect::<Vec<_>>()
            },
            |values| {
                black_box(Validated::sequence(std::mem::take(values), |items| {
                    items.iter().sum::<i32>()
                }));
            },
        );
    }

    // Benchmark iter_errors slice traversal
    let invalid_sample =
        Validated::<i32, String>::invalid_many((0..10).map(|i| format!("err_{i}")));
    group.bench_fn("iter_errors_slice/10", || {
        let mut count = 0;
        for err in invalid_sample.iter_errors() {
            count += err.len();
        }
        black_box(count);
    });
}
