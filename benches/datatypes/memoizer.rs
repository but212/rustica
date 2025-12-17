//! Memoizer benchmarks demonstrating dramatic performance improvements.
//!
//! These benchmarks show how memoization can provide 10x-1000x+ speedups
//! for expensive computations by caching results.

use criterion::{BenchmarkId, Criterion};
use rustica::datatypes::wrapper::memoizer::Memoizer;
use std::hint::black_box;
use std::sync::Arc;
use std::thread;

/// Expensive recursive Fibonacci without memoization - O(2^n)
fn fib_naive(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fib_naive(n - 1) + fib_naive(n - 2),
    }
}

/// Simulates expensive computation (e.g., crypto hash, complex parsing)
fn expensive_computation(input: &u64) -> String {
    // Simulate heavy work: multiple string operations
    let mut result = String::new();
    for i in 0..100 {
        result.push_str(&format!("{}-{}-", input, i));
    }
    // Hash-like transformation
    let hash: u64 = result
        .bytes()
        .fold(0u64, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u64));
    format!("result_{:016x}", hash)
}

/// Prime checking - intentionally slow for demonstration
fn is_prime_slow(n: &u64) -> bool {
    if *n < 2 {
        return false;
    }
    if *n == 2 {
        return true;
    }
    if n.is_multiple_of(2) {
        return false;
    }
    let sqrt = (*n as f64).sqrt() as u64;
    for i in (3..=sqrt).step_by(2) {
        if n.is_multiple_of(i) {
            return false;
        }
        // Artificial slowdown for demo
        std::hint::black_box(i * i);
    }
    true
}

pub fn memoizer_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("memoizer");

    // =========================================================================
    // 1. FIBONACCI: Dramatic O(2^n) → O(1) improvement
    // =========================================================================

    // Naive recursive fibonacci - exponential time O(2^n)
    // black_box on INPUT prevents compile-time constant folding
    group.bench_function("fib_naive_n25", |b| {
        b.iter(|| fib_naive(black_box(25)));
    });

    // Iterative fibonacci with memoization - linear time O(n)
    group.bench_function("fib_memoized_n25_cold", |b| {
        b.iter(|| {
            let memo: Memoizer<u64, u64> = Memoizer::new();
            // Build cache iteratively (bottom-up) - no recursion inside closure
            memo.insert(0, 0);
            memo.insert(1, 1);
            for i in 2..=25 {
                let a = memo.get(&(i - 1)).unwrap();
                let b = memo.get(&(i - 2)).unwrap();
                memo.insert(i, a + b);
            }
            black_box(memo.get(&25))
        });
    });

    // Pre-warmed cache - shows cache hit performance (instant lookup)
    let fib_memo: Memoizer<u64, u64> = Memoizer::new();
    // Build cache outside benchmark loop
    fib_memo.insert(0, 0);
    fib_memo.insert(1, 1);
    for i in 2..=40 {
        let a = fib_memo.get(&(i - 1)).unwrap();
        let b = fib_memo.get(&(i - 2)).unwrap();
        fib_memo.insert(i, a + b);
    }

    group.bench_function("fib_memoized_n25_warm", |b| {
        b.iter(|| black_box(fib_memo.get(&25)));
    });

    // =========================================================================
    // 2. CACHE HIT vs MISS: Direct comparison
    // =========================================================================
    let hit_memo: Memoizer<u64, String> = Memoizer::new();
    // Pre-populate cache
    for i in 0..1000 {
        hit_memo.get_or_compute(i, expensive_computation);
    }

    group.bench_function("cache_hit_1000_lookups", |b| {
        b.iter(|| {
            for i in 0..1000 {
                black_box(hit_memo.get(&i));
            }
        });
    });

    group.bench_function("cache_miss_1000_computes", |b| {
        b.iter(|| {
            let fresh_memo: Memoizer<u64, String> = Memoizer::new();
            for i in 0..1000 {
                black_box(fresh_memo.get_or_compute(i, expensive_computation));
            }
        });
    });

    // =========================================================================
    // 3. EXPENSIVE COMPUTATION: With vs Without memoization
    // =========================================================================
    group.bench_function("expensive_no_memo_100x", |b| {
        b.iter(|| {
            // Same computation 100 times without memoization
            for _ in 0..100 {
                black_box(expensive_computation(&42));
            }
        });
    });

    group.bench_function("expensive_with_memo_100x", |b| {
        let memo: Memoizer<u64, String> = Memoizer::new();
        b.iter(|| {
            // Same computation 100 times with memoization (99 cache hits)
            for _ in 0..100 {
                black_box(memo.get_or_compute(42, expensive_computation));
            }
        });
    });

    // =========================================================================
    // 4. LRU BEHAVIOR: Bounded cache performance
    // =========================================================================
    group.bench_function("lru_bounded_cache", |b| {
        b.iter(|| {
            let memo: Memoizer<u64, u64> = Memoizer::with_capacity(100);
            // Access pattern that triggers evictions
            for i in 0..500 {
                memo.get_or_compute(i, |&n| n * n);
            }
            // Re-access recent items (should be cache hits)
            for i in 400..500 {
                black_box(memo.get_or_compute(i, |&n| n * n));
            }
        });
    });

    group.bench_function("lru_unbounded_cache", |b| {
        b.iter(|| {
            let memo: Memoizer<u64, u64> = Memoizer::new();
            for i in 0..500 {
                memo.get_or_compute(i, |&n| n * n);
            }
            // All items should be cache hits
            for i in 0..500 {
                black_box(memo.get_or_compute(i, |&n| n * n));
            }
        });
    });

    // =========================================================================
    // 5. PRIME CHECKING: Real-world use case
    // =========================================================================
    let large_numbers: Vec<u64> = vec![
        104729, 104723, 104717, 104711, 104707, // primes
        104730, 104724, 104718, 104712, 104708, // non-primes
    ];

    group.bench_function("prime_no_memo_10x", |b| {
        b.iter(|| {
            for _ in 0..10 {
                for n in &large_numbers {
                    black_box(is_prime_slow(n));
                }
            }
        });
    });

    group.bench_function("prime_with_memo_10x", |b| {
        let memo: Memoizer<u64, bool> = Memoizer::new();
        b.iter(|| {
            for _ in 0..10 {
                for n in &large_numbers {
                    black_box(memo.get_or_compute(*n, is_prime_slow));
                }
            }
        });
    });

    // =========================================================================
    // 6. CACHE STATISTICS: Overhead measurement
    // =========================================================================
    group.bench_function("stats_overhead", |b| {
        let memo: Memoizer<u64, u64> = Memoizer::new();
        for i in 0..1000 {
            memo.get_or_compute(i, |&n| n * 2);
        }
        b.iter(|| {
            black_box(memo.stats());
        });
    });

    // =========================================================================
    // 7. SCALING: Different input sizes
    // =========================================================================
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("scaling_populate", size),
            size,
            |b, &size| {
                b.iter(|| {
                    let memo: Memoizer<u64, u64> = Memoizer::new();
                    for i in 0..size {
                        memo.get_or_compute(i as u64, |&n| n * n + n);
                    }
                    black_box(memo.len())
                });
            },
        );
    }

    for size in [10, 100, 1000].iter() {
        let memo: Memoizer<u64, u64> = Memoizer::new();
        for i in 0..*size {
            memo.get_or_compute(i as u64, |&n| n * n + n);
        }
        group.bench_with_input(
            BenchmarkId::new("scaling_lookup", size),
            size,
            |b, &size| {
                b.iter(|| {
                    for i in 0..size {
                        black_box(memo.get(&(i as u64)));
                    }
                });
            },
        );
    }

    // =========================================================================
    // 8. CONCURRENT ACCESS: Multi-threaded performance
    // =========================================================================
    group.bench_function("concurrent_4_threads", |b| {
        b.iter(|| {
            let memo = Arc::new(Memoizer::<u64, u64>::new());
            let handles: Vec<_> = (0..4)
                .map(|t| {
                    let memo = Arc::clone(&memo);
                    thread::spawn(move || {
                        for i in 0..250 {
                            let key = (t * 250 + i) as u64;
                            memo.get_or_compute(key, |&n| n * n);
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }
            black_box(memo.len())
        });
    });

    group.bench_function("concurrent_read_heavy", |b| {
        let memo = Arc::new(Memoizer::<u64, u64>::new());
        // Pre-populate
        for i in 0..1000 {
            memo.get_or_compute(i, |&n| n * n);
        }

        b.iter(|| {
            let handles: Vec<_> = (0..4)
                .map(|_| {
                    let memo = Arc::clone(&memo);
                    thread::spawn(move || {
                        for i in 0..1000 {
                            black_box(memo.get(&(i as u64)));
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // =========================================================================
    // 9. HIT RATE COMPARISON: Different access patterns
    // =========================================================================
    group.bench_function("access_sequential", |b| {
        let memo: Memoizer<u64, u64> = Memoizer::with_capacity(100);
        b.iter(|| {
            // Sequential access - good for LRU
            for round in 0..5 {
                for i in 0..100 {
                    memo.get_or_compute(round * 100 + i, |&n| n * 2);
                }
            }
            black_box(memo.stats().hit_rate())
        });
    });

    group.bench_function("access_repeated", |b| {
        let memo: Memoizer<u64, u64> = Memoizer::with_capacity(100);
        b.iter(|| {
            // Repeated access to same keys - high hit rate
            for _ in 0..5 {
                for i in 0..100 {
                    memo.get_or_compute(i, |&n| n * 2);
                }
            }
            black_box(memo.stats().hit_rate())
        });
    });

    // =========================================================================
    // 10. MEMORY EFFICIENCY: Clear and reuse
    // =========================================================================
    group.bench_function("clear_and_reuse", |b| {
        let memo: Memoizer<u64, String> = Memoizer::new();
        b.iter(|| {
            // Fill cache
            for i in 0..100 {
                memo.get_or_compute(i, expensive_computation);
            }
            // Clear and refill
            memo.clear();
            for i in 0..100 {
                memo.get_or_compute(i, expensive_computation);
            }
            black_box(memo.len())
        });
    });

    group.finish();
}
