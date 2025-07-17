use criterion::Criterion;
use rustica::datatypes::id::Id;
use rustica::traits::applicative::Applicative;
use rustica::traits::comonad::Comonad;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use std::hint::black_box;

pub fn id_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Id");

    // Creation benchmarks
    group.bench_function("id_new", |b| {
        b.iter(|| {
            let id = Id::new(black_box(42));
            black_box(id)
        })
    });

    group.bench_function("id_from_ref", |b| {
        b.iter(|| {
            let value = black_box(42);
            let id = Id::from_ref(&value);
            black_box(id)
        })
    });

    // Functor benchmarks
    group.bench_function("id_fmap", |b| {
        b.iter(|| {
            let id = Id::new(black_box(10));
            let result = id.fmap(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("id_fmap_owned", |b| {
        b.iter(|| {
            let id = Id::new(black_box(10));
            let result = id.fmap_owned(|x| x * 2);
            black_box(result)
        })
    });

    // Applicative benchmarks
    group.bench_function("id_apply", |b| {
        b.iter(|| {
            let id_val = Id::new(black_box(10));
            let id_fn = Id::new(|x: &i32| x * 2);
            let result = id_val.apply(&id_fn);
            black_box(result)
        })
    });

    group.bench_function("id_lift2", |b| {
        b.iter(|| {
            let id1 = Id::new(black_box(10));
            let id2 = Id::new(black_box(20));
            let result = id1.lift2(&id2, |x, y| x + y);
            black_box(result)
        })
    });

    // Monad benchmarks
    group.bench_function("id_bind", |b| {
        b.iter(|| {
            let id = Id::new(black_box(10));
            let result = id.bind(|x| Id::new(x * 2));
            black_box(result)
        })
    });

    group.bench_function("id_join", |b| {
        b.iter(|| {
            let nested_id = Id::new(Id::new(black_box(42)));
            let result: Id<i32> = nested_id.join();
            black_box(result)
        })
    });

    // Comonad benchmarks
    group.bench_function("id_extract", |b| {
        b.iter(|| {
            let id = Id::new(black_box(42));
            let result = id.extract();
            black_box(result)
        })
    });

    group.bench_function("id_duplicate", |b| {
        b.iter(|| {
            let id = Id::new(black_box(42));
            let result = id.duplicate();
            black_box(result)
        })
    });

    group.bench_function("id_extend", |b| {
        b.iter(|| {
            let id = Id::new(black_box(5));
            let result = id.extend(|ctx| {
                let inner_value = *ctx.value();
                inner_value * inner_value
            });
            black_box(result)
        })
    });

    // Semigroup benchmarks (using String which implements Semigroup)
    group.bench_function("id_combine", |b| {
        b.iter(|| {
            let id1 = Id::new(black_box("Hello, ".to_string()));
            let id2 = Id::new(black_box("world!".to_string()));
            let result = id1.combine(&id2);
            black_box(result)
        })
    });

    // Monoid benchmarks (using String which implements Monoid)
    group.bench_function("id_empty", |b| {
        b.iter(|| {
            let result = Id::<String>::empty();
            black_box(result)
        })
    });

    // Identity trait benchmarks
    group.bench_function("id_value", |b| {
        b.iter(|| {
            let id = Id::new(black_box(42));
            let result = *id.value();
            black_box(result)
        })
    });

    group.bench_function("id_into_inner", |b| {
        b.iter(|| {
            let id = Id::new(black_box(42));
            let result = id.into_inner();
            black_box(result)
        })
    });

    // Special operations benchmarks
    group.bench_function("id_then", |b| {
        b.iter(|| {
            let id1 = Id::new(black_box(42));
            let id2 = Id::new(black_box("hello".to_string()));
            let result = id1.then(id2);
            black_box(result)
        })
    });

    group.finish();
}
