use criterion::{black_box, Criterion};
use rustica::datatypes::maybe::Maybe;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use std::collections::HashMap;

// Sample data structures for realistic benchmarks
#[derive(Clone, Debug, PartialEq)]
struct User {
    id: u64,
    name: String,
    email: String,
    active: bool,
}

pub fn maybe_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Maybe");

    // ======== CONSTRUCTION OPERATIONS ========

    group.bench_function("just_creation", |b| {
        b.iter(|| black_box(Maybe::Just(42)));
    });

    group.bench_function("nothing_creation", |b| {
        b.iter(|| black_box(Maybe::<i32>::Nothing));
    });

    group.bench_function("from_option_some", |b| {
        let option = Some(42);
        b.iter(|| black_box(Maybe::from_option(option)));
    });

    group.bench_function("from_option_none", |b| {
        let option: Option<i32> = None;
        b.iter(|| black_box(Maybe::from_option(option)));
    });

    // ======== BASIC OPERATIONS ========

    group.bench_function("is_just", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| black_box(maybe.is_just()));
    });

    group.bench_function("is_nothing", |b| {
        let maybe: Maybe<i32> = Maybe::Nothing;
        b.iter(|| black_box(maybe.is_nothing()));
    });

    group.bench_function("to_option", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| black_box(maybe.to_option()));
    });

    group.bench_function("unwrap", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| {
            // Using a try-catch to prevent panic when benchmarking
            black_box(maybe.unwrap())
        });
    });

    // ======== FUNCTOR OPERATIONS ========

    group.bench_function("fmap", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| black_box(maybe.fmap(|x: &i32| x * 2)));
    });

    group.bench_function("fmap_owned", |b| {
        b.iter(|| black_box(Maybe::Just(42).fmap_owned(|x: i32| x * 2)));
    });

    group.bench_function("fmap_chain", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| black_box(maybe.fmap(|x: &i32| x * 2).fmap(|x: &i32| x + 10)));
    });

    group.bench_function("fmap_nothing", |b| {
        let maybe: Maybe<i32> = Maybe::Nothing;
        b.iter(|| black_box(maybe.fmap(|x: &i32| x * 2)));
    });

    // ======== APPLICATIVE OPERATIONS ========

    group.bench_function("pure", |b| {
        b.iter(|| black_box(Maybe::<i32>::pure(&42)));
    });

    group.bench_function("apply", |b| {
        let maybe = Maybe::Just(42);
        let func = Maybe::Just(|x: &i32| x * 2);
        b.iter(|| black_box(maybe.apply(&func)));
    });

    group.bench_function("apply_owned", |b| {
        b.iter(|| black_box(Maybe::Just(42).apply_owned(Maybe::Just(|x: i32| x * 2))));
    });

    group.bench_function("lift2", |b| {
        let a = Maybe::Just(2);
        let b_value = Maybe::Just(3);
        b.iter(|| black_box(a.lift2(&b_value, |x: &i32, y: &i32| x * y)));
    });

    group.bench_function("lift3", |b| {
        let a = Maybe::Just(2);
        let b_value = Maybe::Just(3);
        let c = Maybe::Just(4);
        b.iter(|| black_box(a.lift3(&b_value, &c, |x: &i32, y: &i32, z: &i32| x * y * z)));
    });

    // ======== MONAD OPERATIONS ========

    group.bench_function("bind", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| black_box(maybe.bind(|x: &i32| Maybe::Just(x * 2))));
    });

    group.bench_function("bind_owned", |b| {
        b.iter(|| black_box(Maybe::Just(42).bind_owned(|x: i32| Maybe::Just(x * 2))));
    });

    group.bench_function("bind_chain", |b| {
        let maybe = Maybe::Just(42);
        b.iter(|| {
            black_box(
                maybe
                    .bind(|x: &i32| Maybe::Just(x * 2))
                    .bind(|x: &i32| Maybe::Just(x + 10)),
            )
        });
    });

    group.bench_function("join", |b| {
        let nested = Maybe::Just(Maybe::Just(42));
        b.iter(|| black_box(nested.join()));
    });

    group.bench_function("join_owned", |b| {
        b.iter(|| black_box(Maybe::Just(Maybe::Just(42)).join_owned()));
    });

    // ======== COMPLEX OPERATIONS ========

    group.bench_function("chain_operations", |b| {
        let maybe = Maybe::Just(10);
        b.iter(|| {
            black_box(
                maybe
                    .fmap(|x: &i32| x + 5)
                    .bind(|x: &i32| {
                        if *x > 10 {
                            Maybe::Just(x * 2)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|x: &i32| x.to_string()),
            )
        });
    });

    group.bench_function("nested_operations", |b| {
        b.iter(|| {
            black_box(Maybe::Just(10).bind(|x: &i32| {
                Maybe::Just(*x * 2)
                    .bind(|y: &i32| Maybe::Just(*y + 5).bind(|z: &i32| Maybe::Just(*z * *z)))
            }))
        });
    });

    // ======== STRING OPERATIONS ========

    group.bench_function("string_operations", |b| {
        let s = "Hello, world!".to_string();
        b.iter(|| {
            black_box(
                Maybe::Just(s.clone())
                    .fmap(|s: &String| s.to_uppercase())
                    .fmap(|s: &String| s.clone() + "!"),
            )
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Use case 1: User lookup with optional fields
    let users: HashMap<u64, User> = {
        let mut map = HashMap::new();
        map.insert(
            1,
            User {
                id: 1,
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
                active: true,
            },
        );
        map.insert(
            2,
            User {
                id: 2,
                name: "Bob".to_string(),
                email: "bob@example.com".to_string(),
                active: false,
            },
        );
        map
    };

    group.bench_function("use_case_user_lookup", |b| {
        let user_id = 1;
        b.iter(|| {
            black_box({
                // Convert Option to Maybe
                let maybe_user = Maybe::from_option(users.get(&user_id).cloned());

                // Only proceed if user is active
                maybe_user
                    .bind(|user: &User| {
                        if user.active {
                            Maybe::Just(user.clone())
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|user: &User| format!("Welcome back, {}!", user.name))
            })
        });
    });

    // Use case 2: Form validation with Maybe
    group.bench_function("use_case_form_validation", |b| {
        // Sample form data
        let email = "user@example.com";
        let age = "25";

        b.iter(|| {
            black_box({
                // Convert inputs and validate
                let valid_email = if email.contains('@') {
                    Maybe::Just(email.to_string())
                } else {
                    Maybe::Nothing
                };

                let valid_age = match age.parse::<u32>() {
                    Ok(n) if n >= 18 && n <= 100 => Maybe::Just(n),
                    _ => Maybe::Nothing,
                };

                // Combine validations with lift2
                valid_email.lift2(&valid_age, |e: &String, a: &u32| {
                    format!("Valid submission: {} is {} years old", e, a)
                })
            })
        });
    });

    // Use case 3: Error handling with Maybe
    group.bench_function("use_case_error_handling", |b| {
        let input = "42";

        b.iter(|| {
            black_box({
                // Parse string to int inside Maybe
                let parsed = match input.parse::<i32>() {
                    Ok(n) => Maybe::Just(n),
                    Err(_) => Maybe::Nothing,
                };

                // Perform chain of operations, early exit on failure
                parsed
                    .bind(|n: &i32| {
                        if *n > 0 {
                            Maybe::Just(*n)
                        } else {
                            Maybe::Nothing // Negative numbers not allowed
                        }
                    })
                    .fmap(|n: &i32| n * 10)
                    .fmap(|n: &i32| format!("Result: {}", n))
            })
        });
    });

    // Use case 4: Processing a sequence with Maybe
    group.bench_function("use_case_sequence_processing", |b| {
        let numbers = vec![1, 2, 3, 4, 5];

        b.iter(|| {
            black_box({
                // Convert a Vec to a Maybe containing first element over threshold
                let find_first_over_threshold = |nums: &[i32], threshold: i32| -> Maybe<i32> {
                    for &n in nums {
                        if n > threshold {
                            return Maybe::Just(n);
                        }
                    }
                    Maybe::Nothing
                };

                // Find first number > 3, then process it
                find_first_over_threshold(&numbers, 3)
                    .fmap(|n: &i32| n * 10)
                    .fmap_or(0, |n| n) // Extract value or default
            })
        });
    });

    // ======== SIZE OPTIMIZATION ========

    group.bench_function("size_optimization", |b| {
        b.iter(|| {
            // Verify null pointer optimization
            black_box(std::mem::size_of::<Maybe<Box<i32>>>() == std::mem::size_of::<Box<i32>>());
            black_box(std::mem::size_of::<Maybe<String>>() == std::mem::size_of::<String>());
            black_box(std::mem::size_of::<Maybe<Vec<i32>>>() == std::mem::size_of::<Vec<i32>>());
        });
    });

    group.finish();
}
