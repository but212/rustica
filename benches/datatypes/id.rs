use criterion::{black_box, Criterion};
use rustica::datatypes::id::Id;
use rustica::traits::applicative::Applicative;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::pure::Pure;
use rustica::traits::semigroup::Semigroup;

pub fn id_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Id");

    // ======== CONSTRUCTION OPERATIONS ========

    group.bench_function("new", |b| {
        b.iter(|| {
            black_box(Id::new(42).into_inner());
        });
    });

    group.bench_function("from_ref", |b| {
        let value = 42;
        b.iter(|| black_box(Id::from_ref(&value).into_inner()));
    });

    group.bench_function("default", |b| {
        b.iter(|| black_box(Id::<String>::default().into_inner()));
    });

    group.bench_function("from_conversion", |b| {
        b.iter(|| {
            let value: Id<i32> = black_box(42.into());
            black_box(value.into_inner())
        });
    });

    // ======== BASIC OPERATIONS ========

    group.bench_function("into_inner", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.clone().into_inner());
        });
    });

    group.bench_function("then", |b| {
        let id1 = Id::new(42);
        let id2 = Id::new("hello");
        b.iter(|| {
            black_box(id1.clone().then(id2.clone()).into_inner());
        });
    });

    // ======== NEW OPTIMIZED OPERATIONS ========

    group.bench_function("as_ref", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.as_ref());
        });
    });

    // ======== IDENTITY OPERATIONS ========

    group.bench_function("identity_value", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.value());
        });
    });

    group.bench_function("pure_identity", |b| {
        b.iter(|| {
            black_box(Id::<i32>::pure_identity(42).into_inner());
        });
    });

    group.bench_function("into_value", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.clone().into_value());
        });
    });

    // ======== FUNCTOR OPERATIONS ========

    group.bench_function("fmap_ref", |b| {
        let id = Id::new(10);
        b.iter(|| black_box(id.fmap(|x: &i32| x * 2).into_inner()));
    });

    group.bench_function("fmap_owned", |b| {
        b.iter(|| black_box(Id::new(10).fmap_owned(|x| x * 2).into_inner()));
    });

    // ======== PURE OPERATIONS ========

    group.bench_function("pure", |b| {
        b.iter(|| {
            black_box(Id::<i32>::pure(&42).into_inner());
        });
    });

    // ======== APPLICATIVE OPERATIONS ========

    group.bench_function("apply", |b| {
        let id_val = Id::new(42);
        let id_fn = Id::new(|x: &i32| x + 1);
        b.iter(|| {
            black_box(id_val.apply(&id_fn).into_inner());
        });
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
        b.iter(|| {
            black_box(id_a.lift2(&id_b, |a: &i32, b: &i32| a + b).into_inner());
        });
    });

    group.bench_function("lift3", |b| {
        let id_a = Id::new(10);
        let id_b = Id::new(20);
        let id_c = Id::new(30);
        b.iter(|| {
            black_box(
                id_a.lift3(&id_b, &id_c, |a: &i32, b: &i32, c: &i32| a + b + c)
                    .into_inner(),
            );
        });
    });

    group.bench_function("lift2_owned", |b| {
        b.iter(|| {
            let id_a = Id::new(10);
            let id_b = Id::new(20);
            black_box(id_a.lift2_owned(id_b, |a: i32, b: i32| a + b).into_inner());
        });
    });

    group.bench_function("lift3_owned", |b| {
        b.iter(|| {
            let id_a = Id::new(10);
            let id_b = Id::new(20);
            let id_c = Id::new(30);
            black_box(
                id_a.lift3_owned(id_b, id_c, |a: i32, b: i32, c: i32| a + b + c)
                    .into_inner(),
            );
        });
    });

    // ======== MONAD OPERATIONS ========

    group.bench_function("bind", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.bind(|x: &i32| Id::new(x + 1)).into_inner());
        });
    });

    group.bench_function("bind_owned", |b| {
        b.iter(|| {
            let id = Id::new(42);
            black_box(id.bind_owned(|x| Id::new(x + 1)).into_inner());
        });
    });

    group.bench_function("join", |b| {
        let id_nested = Id::new(Id::new(42));
        b.iter(|| {
            black_box(id_nested.join::<i32>().into_inner());
        });
    });

    group.bench_function("join_owned", |b| {
        b.iter(|| {
            let id_nested = Id::new(Id::new(42));
            black_box(id_nested.join_owned::<i32>().into_inner());
        });
    });

    // ======== SEMIGROUP & MONOID OPERATIONS ========

    group.bench_function("combine", |b| {
        let id1 = Id::new(String::from("Hello, "));
        let id2 = Id::new(String::from("world!"));
        b.iter(|| {
            black_box(id1.combine(&id2).into_inner());
        });
    });

    group.bench_function("combine_owned", |b| {
        b.iter(|| {
            let id1 = Id::new(String::from("Hello, "));
            let id2 = Id::new(String::from("world!"));
            black_box(id1.combine_owned(id2).into_inner());
        });
    });

    group.bench_function("empty", |b| {
        b.iter(|| {
            black_box(Id::<String>::empty().into_inner());
        });
    });

    // ======== FOLDABLE OPERATIONS ========

    group.bench_function("fold_left", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.fold_left(&String::new(), |acc: &String, x: &i32| {
                acc.clone() + &x.to_string()
            }));
        });
    });

    group.bench_function("fold_right", |b| {
        let id = Id::new(42);
        b.iter(|| {
            black_box(id.fold_right(&String::new(), |x: &i32, acc: &String| x.to_string() + acc));
        });
    });

    // ======== CHAINING OPERATIONS ========

    group.bench_function("chain_operations", |b| {
        let id = Id::new(10);
        b.iter(|| {
            black_box(
                id.fmap(|x: &i32| x + 5)
                    .bind(|x: &i32| Id::new(*x * 2))
                    .fmap(|x: &i32| x.to_string())
                    .into_inner(),
            )
        });
    });

    // ======== PERFORMANCE COMPARISONS ========

    group.bench_function("id_new_vs_clone", |b| {
        let id = Id::new(10);
        b.iter_batched(
            || (),
            |_| {
                let new = Id::new(10);
                let cloned = id.clone();
                black_box((new.into_inner(), cloned.into_inner()))
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // ======== CONST FN OPTIMIZATIONS ========

    group.bench_function("const_new", |b| {
        b.iter(|| {
            // This tests the runtime overhead of a const fn constructor
            black_box(Id::new(10).into_inner())
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Function composition pattern
    group.bench_function("function_composition", |b| {
        // Create a pipeline of transformations
        b.iter(|| {
            let input = Id::new(42);

            // Series of transformations that might represent a data processing pipeline
            let result = input
                .fmap(|x: &i32| x * 2) // Double the input
                .fmap(|x: &i32| x + 10) // Add 10
                .fmap(|x: &i32| if *x > 50 { "large" } else { "small" }) // Categorize
                .fmap(|s: &&str| s.to_uppercase()); // Format output

            black_box(result.into_inner())
        });
    });

    // Data validation pattern
    group.bench_function("data_validation", |b| {
        // Simulate a validation pipeline
        b.iter(|| {
            // Imaginary user input
            let user_data = Id::new((42, "John Doe"));

            // Validate and transform user data in a sequence of operations
            let processed = user_data
                .fmap(|(age, name): &(i32, &str)| {
                    // Validate age
                    let valid_age = *age >= 18;
                    // Validate name
                    let valid_name = !name.is_empty();

                    (valid_age, valid_name, *age, *name)
                })
                .fmap(
                    |(valid_age, valid_name, age, name): &(bool, bool, i32, &str)| {
                        // Summarize validation results
                        if *valid_age && *valid_name {
                            format!("Valid user: {} (age {})", name, age)
                        } else {
                            format!("Invalid user data")
                        }
                    },
                );

            black_box(processed.into_inner())
        });
    });

    // Complex data transformation
    group.bench_function("complex_transformation", |b| {
        b.iter(|| {
            // Start with numerical data
            let data = Id::new(vec![1, 2, 3, 4, 5]);

            // Apply a series of transformations
            let result = data
                .fmap(|v: &Vec<i32>| {
                    // Map: double each value
                    v.iter().map(|x| x * 2).collect::<Vec<i32>>()
                })
                .fmap(|v: &Vec<i32>| {
                    // Filter: keep only values greater than 5
                    v.iter().filter(|&&x| x > 5).cloned().collect::<Vec<i32>>()
                })
                .fmap(|v: &Vec<i32>| {
                    // Reduce: sum all values
                    v.iter().sum::<i32>()
                })
                .fmap(|sum: &i32| {
                    // Format the result
                    format!("The sum is {}", sum)
                });

            black_box(result.into_inner())
        });
    });

    // Monoid-based accumulation pattern
    group.bench_function("monoid_accumulation", |b| {
        b.iter(|| {
            // Create a series of Id<String> values
            let parts = vec![
                Id::new("Hello".to_string()),
                Id::new(", ".to_string()),
                Id::new("world".to_string()),
                Id::new("!".to_string()),
            ];

            // Combine them using monoid operations
            let mut result = Id::<String>::empty();
            for part in &parts {
                result = result.combine(part);
            }

            black_box(result.into_inner())
        });
    });

    // Chained transformations scenario
    group.bench_function("chained_transforms_old", |b| {
        b.iter(|| {
            let id = Id::new(42);
            black_box(
                id.fmap(|x: &i32| x + 10)
                    .fmap(|x: &i32| x * 2)
                    .fmap(|x: &i32| x.to_string())
                    .into_inner(),
            );
        });
    });

    // Fully owned transformation chain
    group.bench_function("owned_transform_chain", |b| {
        b.iter(|| {
            black_box(
                Id::new(42)
                    .fmap(|x| x + 10)
                    .fmap(|x| x * 2)
                    .fmap(|x| x.to_string())
                    .into_inner(),
            );
        });
    });

    // Complex scenario comparing old vs. new patterns
    group.bench_function("complex_scenario_old", |b| {
        b.iter(|| {
            let id = Id::new(10);
            let result = id
                .fmap(|x: &i32| x + 5)
                .bind(|x: &i32| Id::new(x * 2))
                .fmap(|x: &i32| x.to_string());
            black_box(result.into_inner())
        });
    });

    group.bench_function("complex_scenario_optimized", |b| {
        b.iter(|| {
            let id = Id::new(10);
            let result = id
                .fmap_owned(|x| x + 5)
                .bind_owned(|x| Id::new(x * 2))
                .fmap(|x| x.to_string());
            black_box(result.into_inner())
        });
    });

    group.finish();
}
