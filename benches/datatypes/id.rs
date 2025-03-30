use criterion::{black_box, Criterion};
use rustica::datatypes::id::Id;
use rustica::traits::applicative::Applicative;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;

pub fn id_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Id");

    // Construction operations
    group.bench_function("new", |b| {
        b.iter(|| black_box(Id::new(42).into_inner()));
    });

    group.bench_function("from_ref", |b| {
        let value = 42;
        b.iter(|| black_box(Id::from_ref(&value).into_inner()));
    });

    group.bench_function("default", |b| {
        b.iter(|| black_box(Id::<String>::default().into_inner()));
    });

    // Basic operations
    group.bench_function("into_inner", |b| {
        let id = Id::new(42);
        b.iter(|| black_box(id.clone().into_inner()));
    });

    group.bench_function("as_ref", |b| {
        let id = Id::new(42);
        b.iter(|| black_box(id.as_ref()));
    });

    // Identity operations
    group.bench_function("identity_value", |b| {
        let id = Id::new(42);
        b.iter(|| black_box(id.value()));
    });

    group.bench_function("pure_identity", |b| {
        b.iter(|| black_box(Id::<i32>::pure_identity(42).into_inner()));
    });

    // Functor operations
    group.bench_function("fmap_ref", |b| {
        let id = Id::new(10);
        b.iter(|| black_box(id.fmap(|x: &i32| x * 2).into_inner()));
    });

    group.bench_function("fmap_owned", |b| {
        b.iter(|| black_box(Id::new(10).fmap_owned(|x| x * 2).into_inner()));
    });

    // Applicative operations
    group.bench_function("apply", |b| {
        let id_val = Id::new(42);
        let id_fn = Id::new(|x: &i32| x + 1);
        b.iter(|| black_box(id_val.apply(&id_fn).into_inner()));
    });

    group.bench_function("apply_owned", |b| {
        b.iter(|| {
            let id_val = Id::new(42);
            let id_fn = Id::new(|x: i32| x + 1);
            black_box(id_val.apply_owned(id_fn).into_inner());
        });
    });

    group.bench_function("lift2", |b| {
        let id_a = Id::new(10);
        let id_b = Id::new(20);
        b.iter(|| black_box(id_a.lift2(&id_b, |a: &i32, b: &i32| a + b).into_inner()));
    });

    // Monad operations
    group.bench_function("bind", |b| {
        let id = Id::new(42);
        b.iter(|| black_box(id.bind(|x: &i32| Id::new(x + 1)).into_inner()));
    });

    group.bench_function("bind_owned", |b| {
        b.iter(|| {
            let id = Id::new(42);
            black_box(id.bind_owned(|x| Id::new(x + 1)).into_inner());
        });
    });

    group.bench_function("join", |b| {
        let id_nested = Id::new(Id::new(42));
        b.iter(|| black_box(id_nested.join::<i32>().into_inner()));
    });

    // Semigroup & Monoid operations
    group.bench_function("combine", |b| {
        let id1 = Id::new(String::from("Hello, "));
        let id2 = Id::new(String::from("world!"));
        b.iter(|| black_box(id1.combine(&id2).into_inner()));
    });

    group.bench_function("empty", |b| {
        b.iter(|| black_box(Id::<String>::empty().into_inner()));
    });

    // Foldable operations
    group.bench_function("fold_left", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.fold_left(&String::new(), |acc: &String, x: &i32| {
                acc.clone() + &x.to_string()
            }));
        });
    });

    // Real-world use cases
    group.bench_function("function_composition", |b| {
        b.iter(|| {
            let input = Id::new(42);
            let result = input
                .fmap(|x: &i32| x * 2)
                .fmap(|x: &i32| x + 10)
                .fmap(|x: &i32| if *x > 50 { "large" } else { "small" })
                .fmap(|s: &&str| s.to_uppercase());
            black_box(result.into_inner())
        });
    });

    group.bench_function("monoid_accumulation", |b| {
        b.iter(|| {
            let parts = vec![
                Id::new("Hello".to_string()),
                Id::new(", ".to_string()),
                Id::new("world".to_string()),
                Id::new("!".to_string()),
            ];
            let mut result = Id::<String>::empty();
            for part in &parts {
                result = result.combine(part);
            }
            black_box(result.into_inner())
        });
    });

    // Performance comparison patterns
    group.bench_function("reference_vs_owned", |b| {
        b.iter(|| {
            let id = Id::new(10);
            let ref_result = id
                .fmap(|x: &i32| x + 5)
                .bind(|x: &i32| Id::new(x * 2))
                .fmap(|x: &i32| x.to_string());

            let owned_result = Id::new(10)
                .fmap_owned(|x| x + 5)
                .bind_owned(|x| Id::new(x * 2))
                .fmap(|x| x.to_string());

            black_box((ref_result.into_inner(), owned_result.into_inner()))
        });
    });

    group.finish();
}
