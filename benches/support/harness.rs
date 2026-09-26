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
pub const DEFAULT_MEASURE_ITERS: usize = 1000;
/// Default number of routine repetitions per timing sample to amortize timer overhead.
pub const DEFAULT_BATCH_ITERS: usize = 10;

/// Throughput metric for annotated benchmarks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Throughput {
    /// Number of elements processed per operation.
    Elements(u64),
    /// Memory usage in bytes.
    Memory(u64),
}

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

/// A global tracking allocator to measure heap memory allocations.
pub struct TrackingAllocator;
static CURRENT_ALLOCATED: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        CURRENT_ALLOCATED.fetch_add(layout.size(), Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        CURRENT_ALLOCATED.fetch_sub(layout.size(), Ordering::SeqCst);
        unsafe { System.dealloc(ptr, layout) }
    }
}

/// Returns the current number of allocated heap bytes.
#[must_use]
pub fn current_allocated_bytes() -> usize {
    CURRENT_ALLOCATED.load(Ordering::SeqCst)
}

/// A collection of benchmark measurements for a single benchmark group.
pub struct BenchGroup<'a> {
    name: &'a str,
    warmup_iters: usize,
    measure_iters: usize,
    batch_iters: usize,
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
            batch_iters: DEFAULT_BATCH_ITERS,
            throughput: None,
        }
    }

    /// Sets the number of batch iterations per timing sample to amortize timer overhead.
    pub fn batch_iters(&mut self, batch_iters: usize) -> &mut Self {
        self.batch_iters = batch_iters.max(1);
        self
    }

    /// Sets the number of measurement samples.
    pub fn measure_iters(&mut self, measure_iters: usize) -> &mut Self {
        self.measure_iters = measure_iters.max(1);
        self
    }

    /// Sets the number of warmup samples.
    pub fn warmup_iters(&mut self, warmup_iters: usize) -> &mut Self {
        self.warmup_iters = warmup_iters;
        self
    }

    /// Resets iteration and warmup parameters back to defaults.
    pub fn reset_sampling(&mut self) -> &mut Self {
        self.warmup_iters = DEFAULT_WARMUP_ITERS;
        self.measure_iters = DEFAULT_MEASURE_ITERS;
        self.batch_iters = DEFAULT_BATCH_ITERS;
        self
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
            for _ in 0..self.batch_iters {
                routine();
            }
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        let batch_u32 = self.batch_iters as u32;
        for _ in 0..self.measure_iters {
            let start = Instant::now();
            for _ in 0..self.batch_iters {
                routine();
            }
            let elapsed = start.elapsed();
            durations.push(elapsed / batch_u32);
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
            for _ in 0..self.batch_iters {
                routine(input);
            }
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        let batch_u32 = self.batch_iters as u32;
        for _ in 0..self.measure_iters {
            let start = Instant::now();
            for _ in 0..self.batch_iters {
                routine(input);
            }
            let elapsed = start.elapsed();
            durations.push(elapsed / batch_u32);
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
            let mut states: Vec<I> = (0..self.batch_iters).map(|_| setup()).collect();
            for state in &mut states {
                routine(state);
                black_box(state);
            }
        }

        let mut durations = Vec::with_capacity(self.measure_iters);
        let batch_u32 = self.batch_iters as u32;
        for _ in 0..self.measure_iters {
            let mut states: Vec<I> = (0..self.batch_iters).map(|_| setup()).collect();
            let start = Instant::now();
            for state in &mut states {
                routine(state);
            }
            let elapsed = start.elapsed();
            black_box(&states);
            durations.push(elapsed / batch_u32);
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

        let mut sorted = durations.to_vec();
        sorted.sort();

        let min = sorted[0];
        let max = sorted[sorted.len() - 1];

        let median = if sorted.len() % 2 == 1 {
            sorted[sorted.len() / 2]
        } else {
            (sorted[sorted.len() / 2 - 1] + sorted[sorted.len() / 2]) / 2
        };

        let p95_idx = ((sorted.len() as f64 * 0.95).ceil() as usize)
            .saturating_sub(1)
            .min(sorted.len() - 1);
        let p95 = sorted[p95_idx];

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
            Some(Throughput::Memory(bytes)) => {
                if bytes >= 1024 * 1024 {
                    format!(" [{:.2} MB memory]", bytes as f64 / (1024.0 * 1024.0))
                } else {
                    format!(" [{:.2} KB memory]", bytes as f64 / 1024.0)
                }
            },
            None => String::new(),
        };

        println!(
            "{}/{:<30} ... mean: {:>9?} median: {:>9?} p95: {:>9?} min: {:>9?} max: {:>9?} ({} iters){}",
            self.name,
            bench_name,
            mean,
            median,
            p95,
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
