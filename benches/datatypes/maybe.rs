use criterion::{BenchmarkId, Criterion, Throughput};
use rustica::datatypes::maybe::Maybe;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use std::collections::HashMap;
use std::hint::black_box;

// Sample data structures for realistic benchmarks
#[derive(Clone, Debug, PartialEq)]
struct User {
    id: u64,
    name: String,
    email: String,
    active: bool,
}

// Helpers for parameterized benchmarks
fn gen_str(size: usize) -> String {
    "a".repeat(size)
}

fn gen_maybe_vec_ratio(len: usize, percent_just: usize) -> Vec<Maybe<i32>> {
    (0..len)
        .map(|i| {
            if (i % 100) < percent_just {
                Maybe::Just(i as i32)
            } else {
                Maybe::Nothing
            }
        })
        .collect()
}

fn gen_maybe_pairs_ratio(
    len: usize, percent_just_a: usize, percent_just_b: usize,
) -> (Vec<Maybe<i32>>, Vec<Maybe<i32>>) {
    let a: Vec<Maybe<i32>> = (0..len)
        .map(|i| {
            if (i % 100) < percent_just_a {
                Maybe::Just(i as i32)
            } else {
                Maybe::Nothing
            }
        })
        .collect();

    // Offset pattern for b to avoid perfect correlation
    let b: Vec<Maybe<i32>> = (0..len)
        .map(|i| {
            if ((i * 37 + 13) % 100) < percent_just_b {
                Maybe::Just(i as i32)
            } else {
                Maybe::Nothing
            }
        })
        .collect();

    (a, b)
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
            black_box(func.apply(&a));
            black_box(Maybe::Just(|x: i32| x * 2).apply_owned(Maybe::Just(42)));
            black_box(Maybe::<i32>::lift2(|x, y| x * y, &a, &b));
            black_box(Maybe::<i32>::lift3(|x, y, z| x * y * z, &a, &b, &c));
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

    // New: Payload-size sensitivity (Strings)
    for &size in &[0usize, 32, 1_024, 16_384, 262_144] {
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_with_input(
            BenchmarkId::new("fmap_owned_string", size),
            &size,
            |b, &s| {
                let base = gen_str(s);
                b.iter(|| {
                    let m = Maybe::Just(base.clone());
                    black_box(m.fmap_owned(|mut x| {
                        x.push('!');
                        x
                    }))
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("apply_owned_string_len", size),
            &size,
            |b, &s| {
                let base = gen_str(s);
                b.iter(|| {
                    let f = Maybe::Just(|x: String| x.len());
                    black_box(f.apply_owned(Maybe::Just(base.clone())))
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bind_owned_string_chain2", size),
            &size,
            |b, &s| {
                let base = gen_str(s);
                b.iter(|| {
                    black_box(
                        Maybe::Just(base.clone())
                            .bind_owned(|mut x| {
                                x.make_ascii_uppercase();
                                Maybe::Just(x)
                            })
                            .bind_owned(|x| Maybe::Just(x.len())),
                    )
                });
            },
        );
    }

    // New: Distribution sensitivity — Just vs Nothing ratios
    for &len in &[100usize, 10_000] {
        for &p in &[0usize, 25, 50, 75, 100] {
            group.throughput(Throughput::Elements(len as u64));

            group.bench_with_input(
                BenchmarkId::new("fmap_ratio", format!("p{p}_n{len}")),
                &(len, p),
                |b, &(len, p)| {
                    b.iter_batched(
                        || gen_maybe_vec_ratio(len, p),
                        |v| {
                            let mut acc = 0usize;
                            for m in &v {
                                let _ = black_box(m.fmap(|x: &i32| x + 1));
                                acc += 1;
                            }
                            black_box(acc);
                        },
                        criterion::BatchSize::LargeInput,
                    );
                },
            );

            group.bench_with_input(
                BenchmarkId::new("lift2_ratio", format!("p{p}_n{len}")),
                &(len, p),
                |b, &(len, p)| {
                    b.iter_batched(
                        || gen_maybe_pairs_ratio(len, p, p),
                        |(a, b)| {
                            let mut acc = 0usize;
                            for i in 0..a.len() {
                                let _ = black_box(Maybe::<i32>::lift2(|x, y| x + y, &a[i], &b[i]));
                                acc += 1;
                            }
                            black_box(acc);
                        },
                        criterion::BatchSize::LargeInput,
                    );
                },
            );
        }
    }

    // New: Chain length sensitivity and short-circuit behavior
    for &n in &[1usize, 4, 16, 64] {
        group.throughput(Throughput::Elements(n as u64));

        group.bench_with_input(BenchmarkId::new("bind_chain_len", n), &n, |b, &n| {
            b.iter(|| {
                let mut m = Maybe::Just(0);
                for _ in 0..n {
                    m = m.bind(|x: &i32| Maybe::Just(*x + 1));
                }
                black_box(m)
            });
        });

        // Introduce a failure halfway to show early-exit cost
        group.bench_with_input(
            BenchmarkId::new("bind_chain_short_circuit", n),
            &n,
            |b, &n| {
                let fail_at = n / 2;
                b.iter(|| {
                    let mut m = Maybe::Just(0);
                    for i in 0..n {
                        let step = i;
                        m = m.bind(|x: &i32| {
                            if step == fail_at {
                                Maybe::Nothing
                            } else {
                                Maybe::Just(*x + 1)
                            }
                        });
                        if m.is_nothing() {
                            break;
                        }
                    }
                    black_box(m)
                });
            },
        );
    }

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

        let validate_email = |email: &str| -> Maybe<String> {
            if email.contains('@') {
                Maybe::Just(email.to_string())
            } else {
                Maybe::Nothing
            }
        };

        let parse_age = |age: &str| -> Maybe<u32> {
            match age.parse::<u32>() {
                Ok(n) if (18..=100).contains(&n) => Maybe::Just(n),
                _ => Maybe::Nothing,
            }
        };

        let find_threshold = move |threshold: i32| -> Maybe<i32> {
            for &n in &numbers {
                if n > threshold {
                    return Maybe::Just(n);
                }
            }
            Maybe::Nothing
        };

        b.iter(|| {
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

            black_box({
                let valid_email = validate_email(email);
                let valid_age = parse_age(age);
                Maybe::<String>::lift2(
                    |e: &String, a: &u32| format!("Valid submission: {e} is {a} years old"),
                    &valid_email,
                    &valid_age,
                )
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
                    .fmap(|n: &i32| format!("Result: {n}"))
            });

            black_box(find_threshold(3).fmap(|n: &i32| n * 10).fmap_or(0, |n| n));
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
