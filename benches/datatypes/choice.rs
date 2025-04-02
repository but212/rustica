#[cfg(feature = "advanced")]
use criterion::{black_box, Criterion};
#[cfg(feature = "advanced")]
use rustica::datatypes::choice::Choice;
#[cfg(feature = "advanced")]
use rustica::traits::applicative::Applicative;
#[cfg(feature = "advanced")]
use rustica::traits::functor::Functor;
#[cfg(feature = "advanced")]
use rustica::traits::monad::Monad;

#[cfg(feature = "advanced")]
pub fn choice_benchmarks(c: &mut Criterion) {
    // Creation and access operations
    let mut group = c.benchmark_group("Choice - Basic Operations");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(Choice::new(42, vec![1, 2, 3]));
        });
    });

    group.bench_function("empty creation", |b| {
        b.iter(|| {
            black_box(Choice::<i32>::new_empty());
        });
    });

    group.bench_function("of_many creation", |b| {
        b.iter(|| {
            black_box(Choice::of_many(vec![42, 1, 2, 3, 4, 5]));
        });
    });

    group.bench_function("access operations", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box((choice.first(), choice.alternatives(), choice.len()));
        });
    });

    group.finish();

    // Typeclass operations
    let mut group = c.benchmark_group("Choice - Typeclass Operations");

    // Functor
    group.bench_function("fmap", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.fmap(|x: &i32| x + 1));
        });
    });

    group.bench_function("fmap_owned", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.clone().fmap_owned(|x: i32| x + 1));
        });
    });

    // Applicative
    group.bench_function("apply", |b| {
        type FnType = fn(&i32) -> i32;
        let choice_fn = Choice::new(
            FnType::from(|x: &i32| x + 1),
            vec![FnType::from(|x: &i32| x * 2)],
        );
        let choice_val = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(choice_val.apply(&choice_fn));
        });
    });

    // Monad
    group.bench_function("bind", |b| {
        let choice = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(choice.bind(|x: &i32| Choice::new(x + 1, vec![x * 2, x - 1])));
        });
    });

    group.bench_function("bind_owned", |b| {
        let choice = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(
                choice
                    .clone()
                    .bind_owned(|x: i32| Choice::new(x + 1, vec![x * 2, x - 1])),
            );
        });
    });

    group.finish();

    // Modification operations
    let mut group = c.benchmark_group("Choice - Modification Operations");

    group.bench_function("add_alternative", |b| {
        let choice = Choice::new(1, vec![2, 3, 4]);
        b.iter(|| {
            black_box(choice.add_alternative(&5));
        });
    });

    group.bench_function("remove_alternative", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.remove_alternative(2));
        });
    });

    group.bench_function("swap_with_alternative", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.swap_with_alternative(2));
        });
    });

    group.finish();

    // Filtering and transformation
    let mut group = c.benchmark_group("Choice - Filtering and Transformation");

    group.bench_function("filter", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.filter(|&x| x % 2 == 0));
        });
    });

    group.bench_function("fmap_alternatives", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.fmap_alternatives(|&x| x * 2));
        });
    });

    group.bench_function("find_alternative", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.find_alternative(&7));
        });
    });

    group.finish();

    // Real-world use cases
    let mut group = c.benchmark_group("Choice - Practical Applications");

    // Complex operation chain
    group.bench_function("transformation_pipeline", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8]);
        b.iter(|| {
            black_box(
                choice
                    .filter(|&x| x % 2 == 0)
                    .fmap_alternatives(|&x| x * 3)
                    .add_alternative(&99),
            );
        });
    });

    // Multi-criteria decision making
    group.bench_function("multi_criteria_decision", |b| {
        b.iter(|| {
            #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            struct Option {
                id: i32,
                cost: i32,
                quality: i32,
                speed: i32,
            }

            let options = Choice::new(
                Option {
                    id: 1,
                    cost: 100,
                    quality: 7,
                    speed: 5,
                },
                vec![
                    Option {
                        id: 2,
                        cost: 150,
                        quality: 9,
                        speed: 4,
                    },
                    Option {
                        id: 3,
                        cost: 80,
                        quality: 6,
                        speed: 8,
                    },
                ],
            );

            black_box(
                options
                    .filter(|option| option.cost <= 150)
                    .fmap_alternatives(|option| Option {
                        id: option.id,
                        cost: option.cost,
                        quality: option.quality,
                        speed: option.speed + (10 - option.quality),
                    })
                    .bind(|option| {
                        Choice::new(
                            option.clone(),
                            vec![
                                Option {
                                    id: option.id,
                                    cost: 250 - option.cost,
                                    quality: option.quality,
                                    speed: option.speed,
                                },
                                Option {
                                    id: option.id,
                                    cost: option.cost,
                                    quality: option.quality,
                                    speed: option.speed * 2,
                                },
                            ],
                        )
                    }),
            );
        });
    });

    group.bench_function("multi_criteria_decision_owned", |b| {
        b.iter(|| {
            #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            struct Option {
                id: i32,
                cost: i32,
                quality: i32,
                speed: i32,
            }

            let options = Choice::new(
                Option {
                    id: 1,
                    cost: 100,
                    quality: 7,
                    speed: 5,
                },
                vec![
                    Option {
                        id: 2,
                        cost: 150,
                        quality: 9,
                        speed: 4,
                    },
                    Option {
                        id: 3,
                        cost: 80,
                        quality: 6,
                        speed: 8,
                    },
                ],
            );

            black_box(
                options
                    .filter(|option| option.cost <= 150)
                    .fmap_alternatives(|option| Option {
                        id: option.id,
                        cost: option.cost,
                        quality: option.quality,
                        speed: option.speed + (10 - option.quality),
                    })
                    .bind_owned(|option| {
                        Choice::new(
                            option.clone(),
                            vec![
                                Option {
                                    id: option.id,
                                    cost: 250 - option.cost,
                                    quality: option.quality,
                                    speed: option.speed,
                                },
                                Option {
                                    id: option.id,
                                    cost: option.cost,
                                    quality: option.quality,
                                    speed: option.speed * 2,
                                },
                            ],
                        )
                    }),
            );
        });
    });

    // Comparing performance against vector operations
    group.bench_function("compare_with_vector_alternatives", |b| {
        b.iter(|| {
            // Using Choice for alternatives
            let choice = Choice::new(1, vec![2, 3, 4, 5]);
            let result1 = choice.fmap_alternatives(|&x| x * 2);

            // Using vectors directly
            let vec = [1, 2, 3, 4, 5];
            let result2: Vec<_> = vec.iter().map(|&x| x * 2).collect();

            black_box((result1, result2));
        });
    });

    group.finish();
}

#[cfg(not(feature = "advanced"))]
pub fn choice_benchmarks(_c: &mut Criterion) {
    // Benchmarks disabled when advanced feature is not enabled
}
