use crate::harness::Harness;
use rustica::datatypes::choice::Choice;
use std::hint::black_box;

pub fn choice_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("Choice");

    let choice_endpoints = Choice::new(
        "primary.api.com",
        [
            "backup1.api.com",
            "backup2.api.com",
            "backup3.api.com",
            "backup4.api.com",
            "backup5.api.com",
        ],
    );

    group.bench_fn("try_each_primary_hit", || {
        let res: Result<&str, &str> = choice_endpoints.try_each(|ep| {
            if *ep == "primary.api.com" {
                Ok(*ep)
            } else {
                Err("mismatch")
            }
        });
        let _ = black_box(res);
    });

    group.bench_fn("try_each_alt_hit", || {
        let res: Result<&str, &str> = choice_endpoints.try_each(|ep| {
            if *ep == "backup5.api.com" {
                Ok(*ep)
            } else {
                Err("mismatch")
            }
        });
        let _ = black_box(res);
    });

    group.bench_fn("try_each_all_fail", || {
        let res: Result<&str, &str> = choice_endpoints.try_each(|_| Err("unreachable"));
        let _ = black_box(res);
    });

    let numbers = Choice::new(1, [2, 3, 4, 5, 6, 7, 8, 9, 10]);

    group.bench_fn("filter_keep_all", || {
        let filtered = numbers.clone().filter(|x| *x > 0);
        black_box(filtered);
    });

    group.bench_fn("filter_keep_some", || {
        let filtered = numbers.clone().filter(|x| *x % 2 == 0);
        black_box(filtered);
    });
}
