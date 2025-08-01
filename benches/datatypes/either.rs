use criterion::Criterion;
use rustica::datatypes::either::Either;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use std::hint::black_box;

pub fn either_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Either");

    // Creation benchmarks
    group.bench_function("either_left_creation", |b| {
        b.iter(|| {
            let either: Either<i32, String> = Either::left(black_box(42));
            black_box(either)
        })
    });

    group.bench_function("either_right_creation", |b| {
        b.iter(|| {
            let either: Either<i32, String> = Either::right(black_box("test".to_string()));
            black_box(either)
        })
    });

    // Functor benchmarks
    group.bench_function("either_fmap", |b| {
        b.iter(|| {
            let either: Either<String, i32> = Either::right(black_box(10));
            let result = either.fmap(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("either_fmap_left", |b| {
        b.iter(|| {
            let either: Either<i32, String> = Either::left(black_box(10));
            let result = either.fmap_left(|x| x * 2);
            black_box(result)
        })
    });

    // Applicative benchmarks
    group.bench_function("either_apply", |b| {
        b.iter(|| {
            let either_val: Either<String, i32> = Either::right(black_box(10));
            let either_fn: Either<String, fn(&i32) -> i32> = Either::right(|x| x * 2);
            let result = either_fn.apply(&either_val);
            black_box(result)
        })
    });

    group.bench_function("either_lift2", |b| {
        b.iter(|| {
            let either1: Either<String, i32> = Either::right(black_box(10));
            let either2: Either<String, i32> = Either::right(black_box(20));
            let result = Either::<String, i32>::lift2(|x, y| x + y, &either1, &either2);
            black_box(result)
        })
    });

    // Monad benchmarks
    group.bench_function("either_bind", |b| {
        b.iter(|| {
            let either: Either<String, i32> = Either::right(black_box(10));
            let result = either.bind(|x| Either::right(x * 2));
            black_box(result)
        })
    });

    // Special operations benchmarks
    group.bench_function("either_is_left", |b| {
        b.iter(|| {
            let either: Either<i32, String> = Either::left(black_box(42));
            let result = either.is_left();
            black_box(result)
        })
    });

    group.bench_function("either_is_right", |b| {
        b.iter(|| {
            let either: Either<i32, String> = Either::right(black_box("test".to_string()));
            let result = either.is_right();
            black_box(result)
        })
    });

    group.bench_function("either_right_or", |b| {
        b.iter(|| {
            let either: Either<String, i32> = Either::left(black_box("error".to_string()));
            let result = either.right_or(black_box(0));
            black_box(result)
        })
    });

    group.bench_function("either_to_result", |b| {
        b.iter(|| {
            let either: Either<String, i32> = Either::right(black_box(42));
            let result = either.to_result();
            black_box(result)
        })
    });

    group.finish();
}
