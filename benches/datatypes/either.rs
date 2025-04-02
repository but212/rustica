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
        b.iter(|| black_box(Either::<&str, i32>::left(black_box("error"))));
    });

    group.bench_function("right", |b| {
        b.iter(|| black_box(Either::<&str, i32>::right(black_box(42))));
    });

    group.bench_function("pure", |b| {
        b.iter(|| black_box(Either::<&str, i32>::pure(&black_box(42))));
    });

    // ======== BASIC OPERATIONS ========
    let either_left = Either::<&str, i32>::left("error");
    let either_right = Either::<&str, i32>::right(42);

    group.bench_function("is_left", |b| {
        b.iter(|| {
            black_box(either_left.is_left());
            black_box(either_right.is_left());
        });
    });

    group.bench_function("is_right", |b| {
        b.iter(|| {
            black_box(either_left.is_right());
            black_box(either_right.is_right());
        });
    });

    // ======== VALUE ACCESS OPERATIONS ========
    group.bench_function("left_right_ref", |b| {
        b.iter(|| {
            if either_left.is_left() {
                black_box(either_left.left_ref());
            }
            if either_right.is_right() {
                black_box(either_right.right_ref());
            }
        });
    });

    group.bench_function("unwrap_left_right", |b| {
        b.iter(|| {
            if either_left.is_left() {
                black_box(either_left.unwrap_left());
            }
            if either_right.is_right() {
                black_box(either_right.unwrap_right());
            }
        });
    });

    group.bench_function("left_right_value", |b| {
        b.iter(|| {
            if either_left.is_left() {
                black_box(either_left.left_value());
            }
            if either_right.is_right() {
                black_box(either_right.right_value());
            }
        });
    });

    group.bench_function("left_right_or", |b| {
        b.iter(|| {
            black_box(either_left.left_or("default"));
            black_box(either_right.right_or(0));
        });
    });

    // ======== TRANSFORMATION OPERATIONS ========
    group.bench_function("map_left_right", |b| {
        b.iter(|| {
            black_box(either_left.fmap_left(|s| s.len()));
            black_box(either_right.fmap_right(|n| n * 2));
        });
    });

    // ======== FUNCTOR OPERATIONS ========
    group.bench_function("fmap", |b| {
        b.iter(|| {
            black_box(either_left.fmap(|x: &i32| x + 1));
            black_box(either_right.fmap(|x: &i32| x + 1));
        });
    });

    group.bench_function("fmap_owned", |b| {
        b.iter(|| {
            black_box(Either::<&str, i32>::left("error").fmap_owned(|x| x + 1));
            black_box(Either::<&str, i32>::right(42).fmap_owned(|x| x + 1));
        });
    });

    // ======== APPLICATIVE OPERATIONS ========
    group.bench_function("apply", |b| {
        let fn_right = Either::<&str, fn(&i32) -> i32>::right(|x: &i32| x + 1);
        let fn_left = Either::<&str, fn(&i32) -> i32>::left("error");

        b.iter(|| {
            black_box(either_right.apply(&fn_right));
            black_box(either_right.apply(&fn_left));
            black_box(either_left.apply(&fn_right));
        });
    });

    group.bench_function("apply_owned", |b| {
        b.iter(|| {
            let fn_right = Either::<&str, fn(i32) -> i32>::right(|x| x + 1);
            let val_right = Either::<&str, i32>::right(42);
            black_box(val_right.apply_owned(fn_right));
        });
    });

    group.bench_function("lift", |b| {
        let a = Either::<&str, i32>::right(10);
        let c = Either::<&str, i32>::right(20);
        let d = Either::<&str, i32>::right(30);

        b.iter(|| {
            black_box(a.lift2(&c, &|x: &i32, y: &i32| x + y));
            black_box(a.lift3(&c, &d, &|x: &i32, y: &i32, z: &i32| x + y + z));
        });
    });

    group.bench_function("lift_owned", |b| {
        b.iter(|| {
            let a = Either::<&str, i32>::right(10);
            let c = Either::<&str, i32>::right(20);
            let d = Either::<&str, i32>::right(30);
            black_box(a.lift2_owned(c, |x, y| x + y));
            black_box(a.lift3_owned(c, d, |x, y, z| x + y + z));
        });
    });

    // ======== MONAD OPERATIONS ========
    group.bench_function("bind", |b| {
        b.iter(|| {
            black_box(either_right.bind(|x: &i32| Either::<&str, i32>::right(x + 1)));
            black_box(either_left.bind(|x: &i32| Either::<&str, i32>::right(x + 1)));
        });
    });

    group.bench_function("bind_owned", |b| {
        b.iter(|| {
            black_box(
                Either::<&str, i32>::right(42).bind_owned(|x| Either::<&str, i32>::right(x + 1)),
            );
            black_box(
                Either::<&str, i32>::left("error")
                    .bind_owned(|x| Either::<&str, i32>::right(x + 1)),
            );
        });
    });

    group.bench_function("join", |b| {
        let nested = Either::<&str, Either<&str, i32>>::right(Either::<&str, i32>::right(42));
        b.iter(|| black_box(nested.join()));
    });

    group.bench_function("join_owned", |b| {
        b.iter(|| {
            let nested = Either::<&str, Either<&str, i32>>::right(Either::<&str, i32>::right(42));
            black_box(nested.join_owned());
        });
    });

    // ======== IDENTITY OPERATIONS ========
    group.bench_function("identity", |b| {
        b.iter(|| {
            black_box(either_right.value());
            black_box(Either::<&str, i32>::pure_identity(42));
            black_box(Either::<&str, i32>::right(42).into_value());
        });
    });

    // ======== REAL-WORLD USE CASES ========
    group.bench_function("error_handling_chain", |b| {
        b.iter(|| {
            let initial: Either<&str, i32> = Either::right(10);
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

    group.bench_function("data_validation", |b| {
        b.iter(|| {
            let validate = |x: &i32| -> Either<&str, i32> {
                if *x <= 0 {
                    return Either::left("Value must be positive");
                }
                if *x >= 100 {
                    return Either::left("Value must be less than 100");
                }
                Either::right(*x)
            };
            black_box(validate(&42))
        });
    });

    group.bench_function("complex_transformation", |b| {
        b.iter(|| {
            let input: Either<&str, Vec<i32>> = Either::right(vec![1, 2, 3, 4, 5]);
            let result = input
                .fmap(|v: &Vec<i32>| v.iter().map(|x| x * 2).collect::<Vec<i32>>())
                .fmap(|v: &Vec<i32>| {
                    v.iter()
                        .filter(|x| *x % 2 == 0)
                        .cloned()
                        .collect::<Vec<i32>>()
                })
                .fmap(|v: &Vec<i32>| v.iter().sum::<i32>())
                .fmap_right(|sum: i32| if sum > 20 { "large" } else { "small" });
            black_box(result)
        });
    });

    group.bench_function("bidirectional_mapping", |b| {
        b.iter(|| {
            let left = Either::<i32, &str>::left(42);
            let right = Either::<i32, &str>::right("hello");
            black_box((
                left.fmap_left(|n| n * 2).fmap_right(|s| s.len()),
                right.fmap_left(|n| n * 2).fmap_right(|s| s.len()),
            ))
        });
    });

    group.finish();
}
