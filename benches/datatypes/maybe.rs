use criterion::Criterion;
use rustica::datatypes::maybe::Maybe;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use std::hint::black_box;

pub fn maybe_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("maybe");

    // Basic operations - most frequently used
    group.bench_function("basic_ops", |b| {
        let just = Maybe::Just(42);
        let nothing: Maybe<i32> = Maybe::Nothing;
        b.iter(|| {
            black_box(Maybe::Just(42));
            black_box(Maybe::<i32>::Nothing);
            black_box(just.is_just());
            black_box(nothing.is_nothing());
            black_box(just.to_option());
        });
    });

    // Functor operations - core categorical operations
    group.bench_function("functor", |b| {
        let just = Maybe::Just(42);
        let nothing: Maybe<i32> = Maybe::Nothing;
        b.iter(|| {
            black_box(just.fmap(|x: &i32| x * 2));
            black_box(Maybe::Just(42).fmap_owned(|x: i32| x * 2));
            black_box(just.fmap(|x: &i32| x * 2).fmap(|x: &i32| x + 10));
            black_box(nothing.fmap(|x: &i32| x * 2));
        });
    });

    // Applicative operations - core categorical operations
    group.bench_function("applicative", |bench| {
        let a = Maybe::Just(2);
        let b = Maybe::Just(3);
        let func = Maybe::Just(|x: &i32| x * 2);
        bench.iter(|| {
            black_box(Maybe::<i32>::pure(&42));
            black_box(func.apply(&a));
            black_box(Maybe::Just(|x: i32| x * 2).apply_owned(Maybe::Just(42)));
            black_box(Maybe::<i32>::lift2(|x, y| x * y, &a, &b));
        });
    });

    // Monad operations - core categorical operations
    group.bench_function("monad", |b| {
        let maybe = Maybe::Just(42);
        let nested = Maybe::Just(Maybe::Just(42));
        b.iter(|| {
            black_box(maybe.bind(|x: &i32| Maybe::Just(x * 2)));
            black_box(Maybe::Just(42).bind_owned(|x: i32| Maybe::Just(x * 2)));
            black_box(
                maybe
                    .bind(|x: &i32| Maybe::Just(x * 2))
                    .bind(|x: &i32| Maybe::Just(x + 10)),
            );
            black_box(nested.join());
        });
    });

    // Real-world pipeline - practical usage pattern
    group.bench_function("pipeline", |b| {
        b.iter(|| {
            // Validation and transformation pipeline
            let input = "42";
            black_box(
                Maybe::from_option(input.parse::<i32>().ok())
                    .bind(|x: &i32| {
                        if *x > 0 {
                            Maybe::Just(*x)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|x: &i32| x * 2)
                    .fmap(|x: &i32| format!("Result: {x}")),
            );

            // Error handling with early termination
            black_box(
                Maybe::Just(10)
                    .bind(|x: &i32| Maybe::Just(*x * 2))
                    .bind(|y: &i32| {
                        if *y > 15 {
                            Maybe::Just(*y)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|z: &i32| z * z),
            );
        });
    });

    // Memory optimization verification - important for performance
    group.bench_function("memory_layout", |b| {
        b.iter(|| {
            // Verify null pointer optimization works
            black_box(std::mem::size_of::<Maybe<Box<i32>>>() == std::mem::size_of::<Box<i32>>());
            black_box(std::mem::size_of::<Maybe<String>>() == std::mem::size_of::<String>());
            black_box(std::mem::size_of::<Maybe<Vec<i32>>>() == std::mem::size_of::<Vec<i32>>());
        });
    });

    group.finish();
}
