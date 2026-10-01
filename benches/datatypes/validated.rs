use crate::harness::{BenchGroup, Harness};
use rustica::datatypes::validated::Validated;
use rustica::traits::semigroup::Semigroup;
use std::hint::black_box;

fn bench_basic_operations(group: &mut BenchGroup) {
    group.bench_fn("validated_map", || {
        let value = Validated::<i32, String>::valid(42);
        black_box(value.map(|value| value + 1));
    });

    group.bench_fn("result_map", || {
        let value = Result::<i32, String>::Ok(42);
        let _ = black_box(value.map(|value| value + 1));
    });

    // Benchmark sequence single-pass performance (happy path and error path)
    for size in [10_usize, 100_usize] {
        let name_valid = format!("sequence_valid/{size}");
        group.bench_batched(
            &name_valid,
            || {
                (0..size)
                    .map(|i| Validated::<i32, String>::valid(i as i32))
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
                            Validated::valid(i as i32)
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

fn bench_bottlenecks_timing(group: &mut BenchGroup) {
    // 1. collect/from_iter overhead: early error vs all valid vs late error
    for size in [10_usize, 100_usize] {
        // All valid
        group.bench_batched(
            &format!("collect_all_valid/{size}"),
            || {
                (0..size)
                    .map(|i| Validated::<i32, &'static str>::valid(i as i32))
                    .collect::<Vec<_>>()
            },
            |items| {
                let res: Validated<Vec<i32>, &'static str> =
                    Validated::collect(std::mem::take(items).into_iter());
                black_box(res);
            },
        );

        // Early error at index 0: values buffer allocated but abandoned
        group.bench_batched(
            &format!("collect_early_error/{size}"),
            || {
                let mut v: Vec<Validated<i32, &'static str>> = Vec::with_capacity(size);
                v.push(Validated::invalid("early_error"));
                for i in 1..size {
                    v.push(Validated::valid(i as i32));
                }
                v
            },
            |items| {
                let res: Validated<Vec<i32>, &'static str> =
                    Validated::collect(std::mem::take(items).into_iter());
                black_box(res);
            },
        );

        // Late error at the last index: accumulates size - 1 valid values first then discards
        group.bench_batched(
            &format!("collect_late_error/{size}"),
            || {
                let mut v: Vec<Validated<i32, &'static str>> = Vec::with_capacity(size);
                for i in 0..(size - 1) {
                    v.push(Validated::valid(i as i32));
                }
                v.push(Validated::invalid("late_error"));
                v
            },
            |items| {
                let res: Validated<Vec<i32>, &'static str> =
                    Validated::collect(std::mem::take(items).into_iter());
                black_box(res);
            },
        );
    }

    // Regression check: early error with large N (1000) and large payload size ([u64; 16] = 128 bytes)
    group.bench_batched(
        "collect_early_error_1000_large_payload",
        || {
            let mut v: Vec<Validated<[u64; 16], &'static str>> = Vec::with_capacity(1000);
            v.push(Validated::invalid("early_error"));
            for i in 1..1000 {
                v.push(Validated::valid([i as u64; 16]));
            }
            v
        },
        |items| {
            let res: Validated<Vec<[u64; 16]>, &'static str> =
                Validated::collect(std::mem::take(items).into_iter());
            black_box(res);
        },
    );

    // 2. zip3 vs nested zip composition
    group.bench_fn("zip3_all_valid", || {
        let v1 = Validated::<i32, &'static str>::valid(1);
        let v2 = Validated::<i32, &'static str>::valid(2);
        let v3 = Validated::<i32, &'static str>::valid(3);
        black_box(v1.zip3(v2, v3));
    });

    group.bench_fn("zip3_all_invalid", || {
        let v1 = Validated::<i32, &'static str>::invalid("err1");
        let v2 = Validated::<i32, &'static str>::invalid("err2");
        let v3 = Validated::<i32, &'static str>::invalid("err3");
        black_box(v1.zip3(v2, v3));
    });

    // 3. Semigroup combine asymmetry: small (capacity 1) combined with large (capacity 100) vs large with small
    group.bench_batched(
        "combine_asymmetric_small_into_large",
        || {
            let small = Validated::<Vec<i32>, &'static str>::invalid("err_single");
            let large =
                Validated::<Vec<i32>, &'static str>::invalid_many((0..100).map(|_| "err_bulk"));
            (small, large)
        },
        |(small, large)| {
            let s = std::mem::replace(small, Validated::valid(Vec::new()));
            let l = std::mem::replace(large, Validated::valid(Vec::new()));
            black_box(s.combine(l));
        },
    );

    group.bench_batched(
        "combine_asymmetric_large_into_small",
        || {
            let large =
                Validated::<Vec<i32>, &'static str>::invalid_many((0..100).map(|_| "err_bulk"));
            let small = Validated::<Vec<i32>, &'static str>::invalid("err_single");
            (large, small)
        },
        |(large, small)| {
            let l = std::mem::replace(large, Validated::valid(Vec::new()));
            let s = std::mem::replace(small, Validated::valid(Vec::new()));
            black_box(l.combine(s));
        },
    );

    // 4. from_first_and_iter re-allocation overhead vs single invalid
    group.bench_fn("invalid_single", || {
        black_box(Validated::<i32, &'static str>::invalid("single_error"));
    });

    group.bench_fn("invalid_many_from_exact_iter_10", || {
        let iter = ["e0", "e1", "e2", "e3", "e4", "e5", "e6", "e7", "e8", "e9"];
        black_box(Validated::<i32, &'static str>::invalid_many(iter));
    });
}

fn bench_bottlenecks_memory(group: &mut BenchGroup) {
    // 1. Memory churn for collect with late error (discards collected valid values)
    group.bench_memory(
        "mem_collect_late_error_100",
        || {
            let mut v: Vec<Validated<i32, &'static str>> = Vec::with_capacity(100);
            for i in 0..99 {
                v.push(Validated::valid(i));
            }
            v.push(Validated::invalid("last_error"));
            v
        },
        |items| {
            let res: Validated<Vec<i32>, &'static str> =
                Validated::collect(std::mem::take(items).into_iter());
            black_box(res);
        },
    );

    // 2. Memory churn for single error allocation
    group.bench_memory(
        "mem_invalid_single",
        || (),
        |_| {
            let err = Validated::<i32, &'static str>::invalid("single_error");
            black_box(err);
        },
    );

    // 3. Memory churn for asymmetric combine: small.combine(large)
    group.bench_memory(
        "mem_combine_small_into_large",
        || {
            let small = Validated::<Vec<i32>, &'static str>::invalid("err_single");
            let large =
                Validated::<Vec<i32>, &'static str>::invalid_many((0..100).map(|_| "err_bulk"));
            (small, large)
        },
        |(small, large)| {
            let s = std::mem::replace(small, Validated::valid(Vec::new()));
            let l = std::mem::replace(large, Validated::valid(Vec::new()));
            black_box(s.combine(l));
        },
    );

    // 4. Memory churn for zip3 with errors
    group.bench_memory(
        "mem_zip3_all_invalid",
        || (),
        |_| {
            let v1 = Validated::<i32, &'static str>::invalid("err1");
            let v2 = Validated::<i32, &'static str>::invalid("err2");
            let v3 = Validated::<i32, &'static str>::invalid("err3");
            black_box(v1.zip3(v2, v3));
        },
    );

    // 5. Memory churn for early error with large payload (verifies lazy values reservation)
    group.bench_memory(
        "mem_collect_early_error_1000_large_payload",
        || {
            let mut v: Vec<Validated<[u64; 16], &'static str>> = Vec::with_capacity(1000);
            v.push(Validated::invalid("early_error"));
            for i in 1..1000 {
                v.push(Validated::valid([i as u64; 16]));
            }
            v
        },
        |items| {
            let res: Validated<Vec<[u64; 16]>, &'static str> =
                Validated::collect(std::mem::take(items).into_iter());
            black_box(res);
        },
    );
}

pub fn validated_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Validated");
    bench_basic_operations(&mut group);
    bench_bottlenecks_timing(&mut group);
    bench_bottlenecks_memory(&mut group);
}
