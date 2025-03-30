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

    // Construction operations
    group.bench_function("creation", |b| {
        b.iter_batched_ref(
            || (),
            |_| {
                black_box(Maybe::Just(42));
                black_box(Maybe::<i32>::Nothing);
            },
            criterion::BatchSize::SmallInput,
        );
    });

    group.bench_function("from_option", |b| {
        let some_val = Some(42);
        let none_val: Option<i32> = None;
        b.iter(|| {
            black_box(Maybe::from_option(some_val));
            black_box(Maybe::from_option(none_val));
        });
    });

    // Basic operations
    group.bench_function("basic_ops", |b| {
        let just = Maybe::Just(42);
        let nothing: Maybe<i32> = Maybe::Nothing;
        b.iter(|| {
            black_box(just.is_just());
            black_box(nothing.is_nothing());
            black_box(just.to_option());
            black_box(just.unwrap());
        });
    });

    // Functor operations
    group.bench_function("functor_ops", |b| {
        let just = Maybe::Just(42);
        let nothing: Maybe<i32> = Maybe::Nothing;
        b.iter(|| {
            black_box(just.fmap(|x: &i32| x * 2));
            black_box(Maybe::Just(42).fmap_owned(|x: i32| x * 2));
            black_box(just.fmap(|x: &i32| x * 2).fmap(|x: &i32| x + 10));
            black_box(nothing.fmap(|x: &i32| x * 2));
        });
    });

    // Applicative operations
    group.bench_function("applicative_ops", |bench| {
        let a = Maybe::Just(2);
        let b = Maybe::Just(3);
        let c = Maybe::Just(4);
        let func = Maybe::Just(|x: &i32| x * 2);
        bench.iter(|| {
            black_box(Maybe::<i32>::pure(&42));
            black_box(a.apply(&func));
            black_box(Maybe::Just(42).apply_owned(Maybe::Just(|x: i32| x * 2)));
            black_box(a.lift2(&b, |x: &i32, y: &i32| x * y));
            black_box(a.lift3(&b, &c, |x: &i32, y: &i32, z: &i32| x * y * z));
        });
    });

    // Monad operations
    group.bench_function("monad_ops", |b| {
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
            black_box(Maybe::Just(Maybe::Just(42)).join_owned());
        });
    });

    // Complex operations
    group.bench_function("complex_ops", |b| {
        let maybe = Maybe::Just(10);
        let s = "Hello, world!".to_string();
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
            );
            black_box(Maybe::Just(10).bind(|x: &i32| {
                Maybe::Just(*x * 2)
                    .bind(|y: &i32| Maybe::Just(*y + 5).bind(|z: &i32| Maybe::Just(*z * *z)))
            }));
            black_box(
                Maybe::Just(s.clone())
                    .fmap(|s: &String| s.to_uppercase())
                    .fmap(|s: &String| s.clone() + "!"),
            );
        });
    });

    // Real-world use cases
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

    group.bench_function("real_world_use_cases", |b| {
        let user_id = 1;
        let email = "user@example.com";
        let age = "25";
        let numbers = vec![1, 2, 3, 4, 5];

        b.iter(|| {
            // User lookup
            black_box({
                let maybe_user = Maybe::from_option(users.get(&user_id).cloned());
                maybe_user
                    .bind(|user: &User| {
                        if user.active {
                            Maybe::Just(user.clone())
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|user: &User| format!("Welcome back, {}!", user.name))
            });

            // Form validation
            black_box({
                let valid_email = if email.contains('@') {
                    Maybe::Just(email.to_string())
                } else {
                    Maybe::Nothing
                };
                let valid_age = match age.parse::<u32>() {
                    Ok(n) if n >= 18 && n <= 100 => Maybe::Just(n),
                    _ => Maybe::Nothing,
                };
                valid_email.lift2(&valid_age, |e: &String, a: &u32| {
                    format!("Valid submission: {} is {} years old", e, a)
                })
            });

            // Error handling
            black_box({
                let parsed = match "42".parse::<i32>() {
                    Ok(n) => Maybe::Just(n),
                    Err(_) => Maybe::Nothing,
                };
                parsed
                    .bind(|n: &i32| {
                        if *n > 0 {
                            Maybe::Just(*n)
                        } else {
                            Maybe::Nothing
                        }
                    })
                    .fmap(|n: &i32| n * 10)
                    .fmap(|n: &i32| format!("Result: {}", n))
            });

            // Sequence processing
            black_box({
                let find_first_over_threshold = |nums: &[i32], threshold: i32| -> Maybe<i32> {
                    for &n in nums {
                        if n > threshold {
                            return Maybe::Just(n);
                        }
                    }
                    Maybe::Nothing
                };
                find_first_over_threshold(&numbers, 3)
                    .fmap(|n: &i32| n * 10)
                    .fmap_or(0, |n| n)
            });
        });
    });

    // Size optimization
    group.bench_function("size_optimization", |b| {
        b.iter(|| {
            black_box(std::mem::size_of::<Maybe<Box<i32>>>() == std::mem::size_of::<Box<i32>>());
            black_box(std::mem::size_of::<Maybe<String>>() == std::mem::size_of::<String>());
            black_box(std::mem::size_of::<Maybe<Vec<i32>>>() == std::mem::size_of::<Vec<i32>>());
        });
    });

    group.finish();
}
