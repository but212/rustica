use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rustica::datatypes::{
    choice::Choice, either::Either, id::Id, maybe::Maybe, validated::Validated,
};
use rustica::prelude::*;
use std::hint::black_box;

// Core regression benchmarks for critical performance paths
fn benchmark_monad_bind_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("monad_bind_chain");

    // Maybe monad chain
    group.bench_function("maybe", |b| {
        b.iter(|| {
            let m = Maybe::Just(1);
            black_box(
                m.bind(|x| Maybe::Just(x + 1))
                    .bind(|x| Maybe::Just(x * 2))
                    .bind(|x| Maybe::Just(x - 1)),
            )
        })
    });

    // Either monad chain
    group.bench_function("either", |b| {
        b.iter(|| {
            let e: Either<String, i32> = Either::Right(1);
            black_box(
                e.bind(|x| Either::Right(x + 1))
                    .bind(|x| Either::Right(x * 2))
                    .bind(|x| Either::Right(x - 1)),
            )
        })
    });

    // Validated accumulation
    group.bench_function("validated", |b| {
        b.iter(|| {
            let v: Validated<Vec<String>, i32> = Validated::Valid(1);
            black_box(
                v.bind(|x| Validated::Valid(x + 1))
                    .bind(|x| Validated::Valid(x * 2))
                    .bind(|x| Validated::Valid(x - 1)),
            )
        })
    });

    group.finish();
}

fn benchmark_functor_fmap(c: &mut Criterion) {
    let mut group = c.benchmark_group("functor_fmap");

    // Maybe functor
    group.bench_function("maybe", |b| {
        b.iter(|| {
            let m = Maybe::Just(42);
            black_box(m.fmap(|x| x * 2).fmap(|x| x + 1).fmap(|x| x.to_string()))
        })
    });

    // Either functor
    group.bench_function("either", |b| {
        b.iter(|| {
            let e: Either<String, i32> = Either::Right(42);
            black_box(e.fmap(|x| x * 2).fmap(|x| x + 1).fmap(|x| x.to_string()))
        })
    });

    // Id functor
    group.bench_function("id", |b| {
        b.iter(|| {
            let id = Id::new(42);
            black_box(id.fmap(|x| x * 2).fmap(|x| x + 1).fmap(|x| x.to_string()))
        })
    });

    group.finish();
}

fn benchmark_applicative_apply(c: &mut Criterion) {
    let mut group = c.benchmark_group("applicative_apply");

    // Maybe applicative
    group.bench_function("maybe", |b| {
        b.iter(|| {
            let f = Maybe::Just(|x: i32| x * 2);
            let v = Maybe::Just(21);
            black_box(Applicative::apply(f, v))
        })
    });

    // Either applicative
    group.bench_function("either", |b| {
        b.iter(|| {
            let f: Either<String, fn(i32) -> i32> = Either::Right(|x| x * 2);
            let v: Either<String, i32> = Either::Right(21);
            black_box(Applicative::apply(f, v))
        })
    });

    group.finish();
}

fn benchmark_choice_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("choice_operations");

    group.bench_function("choice_select", |b| {
        b.iter(|| {
            let choice = Choice::new(
                Box::new(|x: i32| x + 1),
                vec![Box::new(|x: i32| x * 2), Box::new(|x: i32| x - 1)],
            );
            black_box(choice.fmap(|f| f(42)))
        })
    });

    group.finish();
}

fn benchmark_memory_allocation(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_allocation");

    // Test allocation patterns for different sizes
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("maybe_vec", size), size, |b, &size| {
            b.iter(|| {
                let vec: Vec<Maybe<i32>> = (0..size)
                    .map(|i| {
                        if i % 2 == 0 {
                            Maybe::Just(i)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .collect();
                black_box(
                    vec.into_iter()
                        .map(|m| m.fmap(|x| x * 2))
                        .collect::<Vec<_>>(),
                )
            })
        });
    }

    group.finish();
}

criterion_group!(
    regression_benches,
    benchmark_monad_bind_chain,
    benchmark_functor_fmap,
    benchmark_applicative_apply,
    benchmark_choice_operations,
    benchmark_memory_allocation
);
criterion_main!(regression_benches);
