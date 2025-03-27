use criterion::{black_box, Criterion};
use rustica::datatypes::either::Either;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

pub fn either_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Either");

    // ======== CONSTRUCTION OPERATIONS ========

    group.bench_function("left", |b| {
        b.iter(|| {
            black_box(Either::<&str, i32>::left(black_box("error")));
        });
    });

    group.bench_function("right", |b| {
        b.iter(|| {
            black_box(Either::<&str, i32>::right(black_box(42)));
        });
    });

    group.bench_function("pure", |b| {
        b.iter(|| {
            black_box(Either::<&str, i32>::pure(&black_box(42)));
        });
    });

    // ======== BASIC OPERATIONS ========

    group.bench_function("is_left", |b| {
        let either_left = Either::<&str, i32>::left("error");
        let either_right = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either_left.is_left());
            black_box(either_right.is_left());
        });
    });

    group.bench_function("is_right", |b| {
        let either_left = Either::<&str, i32>::left("error");
        let either_right = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either_left.is_right());
            black_box(either_right.is_right());
        });
    });

    // ======== VALUE ACCESS OPERATIONS ========

    group.bench_function("left_ref", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            if either.is_left() {
                black_box(either.left_ref());
            }
        });
    });

    group.bench_function("right_ref", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            if either.is_right() {
                black_box(either.right_ref());
            }
        });
    });

    group.bench_function("unwrap_left", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            if either.is_left() {
                black_box(either.clone().unwrap_left());
            }
        });
    });

    group.bench_function("unwrap_right", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            if either.is_right() {
                black_box(either.clone().unwrap_right());
            }
        });
    });

    group.bench_function("left_value", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::left("error");
            if either.is_left() {
                black_box(either.left_value());
            }
        });
    });

    group.bench_function("right_value", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::right(42);
            if either.is_right() {
                black_box(either.right_value());
            }
        });
    });

    group.bench_function("left_or", |b| {
        b.iter(|| {
            let either_left = Either::<&str, i32>::left("error");
            let either_right = Either::<&str, i32>::right(42);
            black_box(either_left.clone().left_or("default"));
            black_box(either_right.clone().left_or("default"));
        });
    });

    group.bench_function("right_or", |b| {
        b.iter(|| {
            let either_left = Either::<&str, i32>::left("error");
            let either_right = Either::<&str, i32>::right(42);
            black_box(either_left.clone().right_or(0));
            black_box(either_right.clone().right_or(0));
        });
    });

    // ======== TRANSFORMATION OPERATIONS ========

    group.bench_function("map_left", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            black_box(either.clone().map_left(|s| s.len()));
        });
    });

    group.bench_function("map_right", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either.clone().map_right(|n| n * 2));
        });
    });

    group.bench_function("unwrap_left_safe", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            if either.is_left() {
                black_box(either.clone().unwrap_left());
            }
        });
    });

    group.bench_function("unwrap_right_safe", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            if either.is_right() {
                black_box(either.clone().unwrap_right());
            }
        });
    });

    // ======== FUNCTOR OPERATIONS ========

    group.bench_function("fmap_right", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either.fmap(&|x: &i32| x + 1));
        });
    });

    group.bench_function("fmap_left", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            black_box(either.fmap(&|x: &i32| x + 1));
        });
    });

    group.bench_function("fmap_owned_right", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::right(42);
            black_box(either.fmap_owned(|x| x + 1));
        });
    });

    group.bench_function("fmap_owned_left", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::left("error");
            black_box(either.fmap_owned(|x| x + 1));
        });
    });

    // ======== APPLICATIVE OPERATIONS ========

    group.bench_function("apply_right_right", |b| {
        let either_fn = Either::<&str, fn(&i32) -> i32>::right(|x: &i32| x + 1);
        let either_val = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either_val.apply(&either_fn));
        });
    });

    group.bench_function("apply_left_right", |b| {
        let either_fn = Either::<&str, fn(&i32) -> i32>::left("error");
        let either_val = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either_val.apply(&either_fn));
        });
    });

    group.bench_function("apply_right_left", |b| {
        let either_fn = Either::<&str, fn(&i32) -> i32>::right(|x: &i32| x + 1);
        let either_val = Either::<&str, i32>::left("error");
        b.iter(|| {
            black_box(either_val.apply(&either_fn));
        });
    });

    group.bench_function("apply_owned", |b| {
        b.iter(|| {
            let either_fn = Either::<&str, fn(i32) -> i32>::right(|x| x + 1);
            let either_val = Either::<&str, i32>::right(42);
            black_box(either_val.apply_owned(either_fn));
        });
    });

    group.bench_function("lift2", |b| {
        let either_a = Either::<&str, i32>::right(10);
        let either_b = Either::<&str, i32>::right(20);
        b.iter(|| {
            black_box(either_a.lift2(&either_b, |a: &i32, b: &i32| a + b));
        });
    });

    group.bench_function("lift3", |b| {
        let either_a = Either::<&str, i32>::right(10);
        let either_b = Either::<&str, i32>::right(20);
        let either_c = Either::<&str, i32>::right(30);
        b.iter(|| {
            black_box(either_a.lift3(&either_b, &either_c, |a: &i32, b: &i32, c: &i32| a + b + c));
        });
    });

    group.bench_function("lift2_owned", |b| {
        b.iter(|| {
            let either_a = Either::<&str, i32>::right(10);
            let either_b = Either::<&str, i32>::right(20);
            black_box(either_a.lift2_owned(either_b, |a, b| a + b));
        });
    });

    group.bench_function("lift3_owned", |b| {
        b.iter(|| {
            let either_a = Either::<&str, i32>::right(10);
            let either_b = Either::<&str, i32>::right(20);
            let either_c = Either::<&str, i32>::right(30);
            black_box(either_a.lift3_owned(either_b, either_c, |a, b, c| a + b + c));
        });
    });

    // ======== MONAD OPERATIONS ========

    group.bench_function("bind_right", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either.bind(|x: &i32| Either::<&str, i32>::right(x + 1)));
        });
    });

    group.bench_function("bind_left", |b| {
        let either = Either::<&str, i32>::left("error");
        b.iter(|| {
            black_box(either.bind(|x: &i32| Either::<&str, i32>::right(x + 1)));
        });
    });

    group.bench_function("bind_owned_right", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::right(42);
            black_box(either.bind_owned(|x| Either::<&str, i32>::right(x + 1)));
        });
    });

    group.bench_function("bind_owned_left", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::left("error");
            black_box(either.bind_owned(|x| Either::<&str, i32>::right(x + 1)));
        });
    });

    group.bench_function("join", |b| {
        let nested = Either::<&str, Either<&str, i32>>::right(Either::<&str, i32>::right(42));
        b.iter(|| {
            black_box(nested.join());
        });
    });

    group.bench_function("join_owned", |b| {
        b.iter(|| {
            let nested = Either::<&str, Either<&str, i32>>::right(Either::<&str, i32>::right(42));
            black_box(nested.join_owned());
        });
    });

    // ======== IDENTITY OPERATIONS ========

    group.bench_function("identity_value", |b| {
        let either = Either::<&str, i32>::right(42);
        b.iter(|| {
            black_box(either.value());
        });
    });

    group.bench_function("pure_identity", |b| {
        b.iter(|| {
            black_box(Either::<&str, i32>::pure_identity(42));
        });
    });

    group.bench_function("into_value", |b| {
        b.iter(|| {
            let either = Either::<&str, i32>::right(42);
            black_box(either.into_value());
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Error handling use case
    group.bench_function("error_handling", |b| {
        b.iter(|| {
            // Simulate a series of operations that might fail
            let initial: Either<&str, i32> = Either::right(10);

            // Chain operations using bind
            let result = initial
                .bind(|x: &i32| {
                    if *x > 0 {
                        Either::right(x * 2)
                    } else {
                        Either::left("Cannot multiply negative number")
                    }
                })
                .bind(|x: &i32| {
                    if *x < 100 {
                        Either::right(x + 5)
                    } else {
                        Either::left("Result too large")
                    }
                })
                .fmap(&|x: &i32| x.to_string());

            black_box(result)
        });
    });

    // Error handling use case with optimized methods
    group.bench_function("error_handling_optimized", |b| {
        b.iter(|| {
            // Simulate a series of operations that might fail
            let initial: Either<&str, i32> = Either::right(10);

            // Chain operations using bind_owned
            let result = initial
                .bind_owned(|x| {
                    if x > 0 {
                        Either::right(x * 2)
                    } else {
                        Either::left("Cannot multiply negative number")
                    }
                })
                .bind_owned(|x| {
                    if x < 100 {
                        Either::right(x + 5)
                    } else {
                        Either::left("Result too large")
                    }
                })
                .fmap_owned(|x| x.to_string());

            black_box(result)
        });
    });

    // Data validation use case
    group.bench_function("data_validation", |b| {
        b.iter(|| {
            // Validators that return Either
            let validate_positive = |x: &i32| -> Either<&str, i32> {
                if *x > 0 {
                    Either::right(*x)
                } else {
                    Either::left("Value must be positive")
                }
            };

            let validate_less_than_100 = |x: &i32| -> Either<&str, i32> {
                if *x < 100 {
                    Either::right(*x)
                } else {
                    Either::left("Value must be less than 100")
                }
            };

            // Apply validators in sequence
            let input = 42;
            let result = validate_positive(&input).bind(|x: &i32| validate_less_than_100(x));

            black_box(result)
        });
    });

    // Complex transformation chain
    group.bench_function("complex_transformation", |b| {
        b.iter(|| {
            let input: Either<&str, Vec<i32>> = Either::right(vec![1, 2, 3, 4, 5]);

            // Apply multiple transformations
            let result = input
                .fmap(&|v: &Vec<i32>| v.iter().map(|x| x * 2).collect::<Vec<i32>>())
                .fmap(&|v: &Vec<i32>| {
                    v.iter()
                        .filter(|x| *x % 2 == 0)
                        .cloned()
                        .collect::<Vec<i32>>()
                })
                .fmap(&|v: &Vec<i32>| v.iter().sum::<i32>())
                .map_right(|sum: &i32| if *sum > 20 { "large" } else { "small" });

            black_box(result)
        });
    });

    // Value extraction with the new methods
    group.bench_function("value_extraction_optimized", |b| {
        b.iter(|| {
            let left_val = Either::<&str, i32>::left("error");
            let right_val = Either::<&str, i32>::right(42);

            // Using right_or and left_or
            let left_result = left_val.clone().left_or("default");
            let right_result = right_val.clone().right_or(0);

            black_box((left_result, right_result))
        });
    });

    // Bidirectional mapping use case
    group.bench_function("bidirectional_mapping", |b| {
        b.iter(|| {
            let left_value: Either<i32, &str> = Either::left(42);
            let right_value: Either<i32, &str> = Either::right("hello");

            // Map both sides
            let mapped_left = left_value
                .clone()
                .map_left(|n| n * 2)
                .map_right(|s| s.len());

            let mapped_right = right_value.map_left(|n| n * 2).map_right(|s| s.len());

            black_box((mapped_left, mapped_right))
        });
    });

    group.finish();
}
