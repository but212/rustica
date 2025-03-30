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
use rustica::traits::pure::Pure;

#[cfg(feature = "advanced")]
pub fn choice_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Creation and Access Operations
    let mut group = c.benchmark_group("Choice - Creation and Access");

    group.bench_function("pure", |b| {
        b.iter(|| {
            black_box(Choice::<i32>::pure(&42));
        });
    });

    group.bench_function("new with few alternatives", |b| {
        b.iter(|| {
            black_box(Choice::new(42, vec![1, 2, 3]));
        });
    });

    group.bench_function("new with many alternatives", |b| {
        b.iter(|| {
            black_box(Choice::new(42, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]));
        });
    });

    group.bench_function("new_empty", |b| {
        b.iter(|| {
            black_box(Choice::<i32>::new_empty());
        });
    });

    group.bench_function("of_many", |b| {
        b.iter(|| {
            black_box(Choice::of_many(vec![42, 1, 2, 3, 4, 5]));
        });
    });

    group.bench_function("from_iterator - non-empty", |b| {
        let items = vec![1, 2, 3, 4, 5];
        b.iter(|| {
            black_box(Choice::from_iterator(items.clone()));
        });
    });

    group.bench_function("from_iterator - empty", |b| {
        let items: Vec<i32> = Vec::new();
        b.iter(|| {
            black_box(Choice::from_iterator(items.clone()));
        });
    });

    group.bench_function("first access", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.first());
        });
    });

    group.bench_function("alternatives access", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.alternatives());
        });
    });

    group.bench_function("has_alternatives", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.has_alternatives());
        });
    });

    group.bench_function("len", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.len());
        });
    });

    group.bench_function("is_empty on non-empty", |b| {
        let choice = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(choice.is_empty());
        });
    });

    group.bench_function("is_empty on empty", |b| {
        let choice = Choice::<i32>::new_empty();
        b.iter(|| {
            black_box(choice.is_empty());
        });
    });

    group.finish();

    // Section 2: Typeclass Operations (Functor, Applicative, Monad)
    let mut group = c.benchmark_group("Choice - Type Class Operations");

    // Functor operations
    group.bench_function("fmap with simple values", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.fmap(|x: &i32| x + 1));
        });
    });

    group.bench_function("fmap with complex function", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.fmap(|x: &i32| {
                let mut result = 0;
                for i in 0..*x {
                    result += i;
                }
                result
            }));
        });
    });

    group.bench_function("fmap with type conversion", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.fmap(|x: &i32| x.to_string()));
        });
    });

    group.bench_function("chained fmaps", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5]);
        b.iter(|| {
            black_box(
                choice
                    .fmap(|x: &i32| x * 2)
                    .fmap(|x: &i32| x + 10)
                    .fmap(|x: &i32| x - 5),
            );
        });
    });

    // Applicative operations
    group.bench_function("apply with simple function", |b| {
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

    group.bench_function("apply with multiple functions", |b| {
        type FnType = fn(&i32) -> i32;
        let choice_fn = Choice::new(
            FnType::from(|x: &i32| x + 1),
            vec![
                FnType::from(|x: &i32| x * 2),
                FnType::from(|x: &i32| x - 5),
                FnType::from(|x: &i32| x * x),
            ],
        );
        let choice_val = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(choice_val.apply(&choice_fn));
        });
    });

    group.bench_function("apply with multiple values", |b| {
        type FnType = fn(&i32) -> i32;
        let choice_fn = Choice::new(
            FnType::from(|x: &i32| x + 1),
            vec![FnType::from(|x: &i32| x * 2)],
        );
        let choice_val = Choice::new(42, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice_val.apply(&choice_fn));
        });
    });

    // Monad operations
    group.bench_function("bind with simple function", |b| {
        let choice = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(choice.bind(|x: &i32| Choice::new(x + 1, vec![x * 2, x - 1])));
        });
    });

    group.bench_function("bind with conditional logic", |b| {
        let choice = Choice::new(42, vec![1, 2, 3, 4, 5, 6]);
        b.iter(|| {
            black_box(choice.bind(|x: &i32| {
                if x % 2 == 0 {
                    Choice::new(x * 2, vec![x + 10])
                } else {
                    Choice::new(x - 1, vec![x * 3])
                }
            }));
        });
    });

    group.bench_function("chained binds", |b| {
        let choice = Choice::new(42, vec![1, 2, 3]);
        b.iter(|| {
            black_box(
                choice
                    .bind(|x: &i32| Choice::new(x + 1, vec![x * 2]))
                    .bind(|x: &i32| Choice::new(x - 5, vec![x / 2]))
                    .bind(|x: &i32| Choice::new(x * 3, vec![x + 10])),
            );
        });
    });

    group.finish();

    // Section 3: Modification Operations
    let mut group = c.benchmark_group("Choice - Modification Operations");

    group.bench_function("change_first", |b| {
        let choice = Choice::new(1, vec![2, 3, 4]);
        b.iter(|| {
            black_box(choice.change_first(&42));
        });
    });

    group.bench_function("add_alternative", |b| {
        let choice = Choice::new(1, vec![2, 3, 4]);
        b.iter(|| {
            black_box(choice.add_alternative(&5));
        });
    });

    group.bench_function("add_alternatives_owned with few items", |b| {
        b.iter(|| {
            let choice = Choice::new(1, vec![2, 3]);
            black_box(choice.add_alternatives_owned(vec![4, 5, 6]));
        });
    });

    group.bench_function("add_alternatives_owned with many items", |b| {
        b.iter(|| {
            let choice = Choice::new(1, vec![2, 3]);
            black_box(choice.add_alternatives_owned(vec![4, 5, 6, 7, 8, 9, 10, 11, 12, 13]));
        });
    });

    group.bench_function("remove_alternative from beginning", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.remove_alternative(0));
        });
    });

    group.bench_function("remove_alternative from middle", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.remove_alternative(2));
        });
    });

    group.bench_function("remove_alternative from end", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.remove_alternative(3));
        });
    });

    group.bench_function("swap_with_alternative beginning", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.swap_with_alternative(0));
        });
    });

    group.bench_function("swap_with_alternative middle", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.swap_with_alternative(2));
        });
    });

    group.bench_function("swap_with_alternative end", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.swap_with_alternative(3));
        });
    });

    group.bench_function("swap_with_alternative_owned", |b| {
        b.iter(|| {
            let choice = Choice::new(1, vec![2, 3, 4, 5]);
            black_box(choice.swap_with_alternative_owned(2));
        });
    });

    group.finish();

    // Section 4: Filtering and Transformation
    let mut group = c.benchmark_group("Choice - Filtering and Transformation");

    group.bench_function("filter simple predicate", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.filter(|&x| x % 2 == 0));
        });
    });

    group.bench_function("filter complex predicate", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
        b.iter(|| {
            black_box(choice.filter(|&x| {
                let mut sum = 0;
                let mut n = x;
                while n > 0 {
                    sum += n % 10;
                    n /= 10;
                }
                sum % 3 == 0
            }));
        });
    });

    group.bench_function("map_alternatives simple transformation", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.map_alternatives(|&x| x * 2));
        });
    });

    group.bench_function("map_alternatives complex transformation", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.map_alternatives(|&x| {
                let mut result = 1;
                for i in 1..=x {
                    result *= i;
                }
                result
            }));
        });
    });

    group.bench_function("map_alternatives with type conversion", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5]);
        b.iter(|| {
            black_box(choice.map_alternatives(|&x| x.to_string()));
        });
    });

    group.bench_function("find_alternative existing at beginning", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.find_alternative(&2));
        });
    });

    group.bench_function("find_alternative existing at middle", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.find_alternative(&7));
        });
    });

    group.bench_function("find_alternative existing at end", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.find_alternative(&10));
        });
    });

    group.bench_function("find_alternative non-existing", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10]);
        b.iter(|| {
            black_box(choice.find_alternative(&42));
        });
    });

    group.finish();

    // Section 5: Collection Operations
    let mut group = c.benchmark_group("Choice - Collection Operations");

    group.bench_function("flatten small nested collections", |b| {
        let nested = Choice::new(vec![1, 2], vec![vec![3, 4], vec![5, 6]]);
        b.iter(|| {
            black_box(nested.flatten());
        });
    });

    group.bench_function("flatten large nested collections", |b| {
        let nested = Choice::new(
            vec![1, 2, 3, 4, 5],
            vec![
                vec![6, 7, 8, 9, 10],
                vec![11, 12, 13, 14, 15],
                vec![16, 17, 18, 19, 20],
            ],
        );
        b.iter(|| {
            black_box(nested.flatten());
        });
    });

    group.finish();

    // Section 6: Real-world Use Cases
    let mut group = c.benchmark_group("Choice - Real-world Use Cases");

    // Complex operation chains common in functional programming
    group.bench_function("data transformation pipeline", |b| {
        let choice = Choice::new(1, vec![2, 3, 4, 5, 6, 7, 8]);
        b.iter(|| {
            black_box(
                choice
                    .filter(|&x| x % 2 == 0) // Keep only even alternatives
                    .map_alternatives(|&x| x * 3) // Triple each value
                    .add_alternative(&99), // Add another alternative
            );
        });
    });

    // Representing search paths
    group.bench_function("search path exploration", |b| {
        b.iter(|| {
            // Simulating a search algorithm that explores different paths
            let initial_paths = Choice::new(
                vec![1, 2],                               // Primary path
                vec![vec![1, 3], vec![1, 4], vec![1, 5]], // Alternative paths
            );

            black_box(
                initial_paths
                    .flatten() // Flatten to get all possible next steps
                    .bind(|&node| {
                        // For each node, generate possible next steps
                        if node % 2 == 0 {
                            Choice::new(node * 2, vec![node + 1, node + 2])
                        } else {
                            Choice::new(node + 10, vec![node * 3, node - 1])
                        }
                    }),
            );
        });
    });

    // Non-deterministic computation
    group.bench_function("non-deterministic computation", |b| {
        b.iter(|| {
            // Starting with some initial values
            let values = Choice::new(5, vec![10, 15, 20, 25]);

            black_box(
                values
                    // Apply first computation which produces multiple results
                    .bind(|&x| Choice::new(x + 1, vec![x - 1, x * 2]))
                    // Apply second computation
                    .bind(|&x| {
                        if x > 20 {
                            Choice::new(x / 2, vec![x - 10])
                        } else {
                            Choice::new(x * 3, vec![x + 5])
                        }
                    })
                    // Filter results
                    .filter(|&x| x > 15 && x < 50)
                    .iter_alternatives()
                    .collect::<Vec<_>>(),
            );
        });
    });

    // Decision tree evaluation
    group.bench_function("decision tree evaluation", |b| {
        b.iter(|| {
            // Define a tree of decision options
            type Decision = i32;

            // Initial decision with alternatives
            let decisions = Choice::new(1, vec![2, 3, 4]); // Decision IDs

            black_box(
                decisions
                    .bind(|&decision: &Decision| {
                        // For each decision, evaluate outcomes
                        match decision {
                            1 => Choice::new(10, vec![15, 20]),     // Option 1 outcomes
                            2 => Choice::new(25, vec![30]),         // Option 2 outcomes
                            3 => Choice::new(35, vec![40, 45]),     // Option 3 outcomes
                            4 => Choice::new(50, vec![55, 60, 65]), // Option 4 outcomes
                            _ => Choice::new(0, vec![]),            // Invalid decision
                        }
                    })
                    .bind(|&outcome| {
                        // Calculate utility for each outcome
                        let base_utility = outcome / 5;

                        if outcome > 40 {
                            Choice::new(base_utility * 2, vec![base_utility + 5])
                        } else {
                            Choice::new(base_utility, vec![base_utility / 2, base_utility + 2])
                        }
                    })
                    .iter_alternatives()
                    .collect::<Vec<_>>(),
            );
        });
    });

    // Multi-criteria decision making
    group.bench_function("multi-criteria evaluation", |b| {
        b.iter(|| {
            // Represents options with multiple criteria scores
            #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            struct Option {
                id: i32,
                cost: i32,
                quality: i32,
                speed: i32,
            }

            // Initial options
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
                    Option {
                        id: 4,
                        cost: 120,
                        quality: 8,
                        speed: 6,
                    },
                    Option {
                        id: 5,
                        cost: 200,
                        quality: 10,
                        speed: 3,
                    },
                ],
            );

            black_box(
                options
                    // First filter by cost
                    .filter(|option| option.cost <= 150)
                    // Map to weighted scores
                    .map_alternatives(|option| {
                        Option {
                            id: option.id,
                            cost: option.cost,
                            quality: option.quality,
                            // Calculate weighted score
                            speed: option.speed + (10 - option.quality),
                        }
                    })
                    // Find best by different criteria
                    .bind(|option| {
                        // Create choices based on different ranking methods
                        Choice::new(
                            // By quality
                            option.clone(),
                            vec![
                                // By cost (lowest)
                                Option {
                                    id: option.id,
                                    // Invert cost for ranking (lower is better)
                                    cost: 250 - option.cost,
                                    quality: option.quality,
                                    speed: option.speed,
                                },
                                // By speed
                                Option {
                                    id: option.id,
                                    cost: option.cost,
                                    quality: option.quality,
                                    // Emphasize speed
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
            let result1 = choice.map_alternatives(|&x| x * 2);

            // Using vectors directly
            let vec = vec![1, 2, 3, 4, 5];
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
