//! Minimalist zero-dependency benchmark harness for benchmarks.
//!
//! Provides lightweight benchmarking functionality measuring execution time
//! using standard library primitives (std::time::Instant and std::hint::black_box).

use std::fmt::Display;
use std::hint::black_box;
use std::time::{Duration, Instant};

/// Default number of warmup iterations before measurement.
pub const DEFAULT_WARMUP_ITERS: usize = 10;
/// Default number of measurement iterations.
pub const DEFAULT_MEASURE_ITERS: usize = 100;

/// Throughput metric for annotated benchmarks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Throughput {
    /// Number of elements processed per operation.
    Elements(u64),
    /// Number of bytes processed per operation.
    Bytes(u64),
}

/// A collection of benchmark measurements for a single benchmark group.
pub struct BenchGroup<'a> {
    name: &'a str,
    warmup_iters: usize,
    measure_iters: usize,
    throughput: Option<Throughput>,
}

impl<'a> BenchGroup<'a> {
    /// Creates a new benchmark group with the given name.
    #[must_use]
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            warmup_iters: DEFAULT_WARMUP_ITERS,
            measure_iters: DEFAULT_MEASURE_ITERS,
            throughput: None,
        }
    }

    /// Sets the throughput annotation for subsequent benchmarks in this group.
    pub fn throughput(&mut self, throughput: Throughput) -> &mut Self {
        self.throughput = Some(throughput);
        self
    }

    /// Clears any throughput annotation for subsequent benchmarks in this group.
    pub fn clear_throughput(&mut self) -> &mut Self {
        self.throughput = None;
        self
    }

    /// Runs a benchmark function measuring the closure execution.
    pub fn bench_fn<F>(&mut self, bench_name: &str, mut routine: F)
    where
        F: FnMut(),
    {
        for _ in 0..self.warmup_iters {
            routine();
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        for _ in 0..self.measure_iters {
            let start = Instant::now();
            routine();
            let elapsed = start.elapsed();
            durations.push(elapsed);
        }

        self.report_results(bench_name, &durations);
    }

    /// Runs a parameterized benchmark function with a given input.
    pub fn bench_with_input<I, F>(&mut self, bench_name: &str, input: &I, mut routine: F)
    where
        I: Display + ?Sized,
        F: FnMut(&I),
    {
        let full_name = format!("{bench_name}/{input}");
        for _ in 0..self.warmup_iters {
            routine(input);
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        for _ in 0..self.measure_iters {
            let start = Instant::now();
            routine(input);
            let elapsed = start.elapsed();
            durations.push(elapsed);
        }

        self.report_results(&full_name, &durations);
    }

    /// Runs a batched benchmark where a setup function generates fresh state
    /// for each iteration without including the setup cost in the timing.
    pub fn bench_batched<I, S, R>(&mut self, bench_name: &str, mut setup: S, mut routine: R)
    where
        S: FnMut() -> I,
        R: FnMut(&mut I),
    {
        for _ in 0..self.warmup_iters {
            let mut state = setup();
            routine(&mut state);
            black_box(state);
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        for _ in 0..self.measure_iters {
            let mut state = setup();
            let start = Instant::now();
            routine(&mut state);
            let elapsed = start.elapsed();
            durations.push(elapsed);
            black_box(state);
        }

        self.report_results(bench_name, &durations);
    }

    fn report_results(&self, bench_name: &str, durations: &[Duration]) {
        if durations.is_empty() {
            return;
        }

        let total: Duration = durations.iter().copied().sum();
        let count = durations.len() as u32;
        let mean = total / count;
        let min = durations.iter().copied().min().unwrap_or_default();
        let max = durations.iter().copied().max().unwrap_or_default();

        let throughput_str = match self.throughput {
            Some(Throughput::Elements(elements)) => {
                let mean_secs = mean.as_secs_f64();
                if mean_secs > 0.0 {
                    let elem_per_sec = elements as f64 / mean_secs;
                    format!(" [{:.2} M elem/s]", elem_per_sec / 1_000_000.0)
                } else {
                    String::new()
                }
            },
            Some(Throughput::Bytes(bytes)) => {
                let mean_secs = mean.as_secs_f64();
                if mean_secs > 0.0 {
                    let mb_per_sec = (bytes as f64 / (1024.0 * 1024.0)) / mean_secs;
                    format!(" [{mb_per_sec:.2} MB/s]")
                } else {
                    String::new()
                }
            },
            None => String::new(),
        };

        println!(
            "{}/{:<30} ... mean: {:>10?} min: {:>10?} max: {:>10?} ({} iters){}",
            self.name,
            bench_name,
            mean,
            min,
            max,
            durations.len(),
            throughput_str
        );
    }
}

/// Benchmark harness entry point.
#[derive(Default)]
pub struct Harness;

impl Harness {
    /// Creates a new benchmark harness.
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Starts a new benchmark group.
    #[must_use]
    pub fn benchmark_group<'a>(&self, name: &'a str) -> BenchGroup<'a> {
        BenchGroup::new(name)
    }
}
