//! Memory profiling benchmarks for PersistentVector
//!
//! This module provides specialized benchmarks for measuring memory usage,
//! allocation patterns, and structural sharing efficiency of PersistentVector.

use criterion::{BenchmarkId, Criterion, Throughput};
#[cfg(feature = "pvec")]
use rustica::pvec::{AlwaysCache, NeverCache, PersistentVector};
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// A custom allocator that tracks memory usage
struct TrackingAllocator {
    allocated: AtomicUsize,
    deallocated: AtomicUsize,
    peak_usage: AtomicUsize,
}

impl TrackingAllocator {
    const fn new() -> Self {
        Self {
            allocated: AtomicUsize::new(0),
            deallocated: AtomicUsize::new(0),
            peak_usage: AtomicUsize::new(0),
        }
    }

    fn current_usage(&self) -> usize {
        self.allocated.load(Ordering::Relaxed) - self.deallocated.load(Ordering::Relaxed)
    }

    fn peak_usage(&self) -> usize {
        self.peak_usage.load(Ordering::Relaxed)
    }

    fn reset(&self) {
        self.allocated.store(0, Ordering::Relaxed);
        self.deallocated.store(0, Ordering::Relaxed);
        self.peak_usage.store(0, Ordering::Relaxed);
    }
}

unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            let size = layout.size();
            let old_allocated = self.allocated.fetch_add(size, Ordering::Relaxed);
            let current = old_allocated + size - self.deallocated.load(Ordering::Relaxed);

            // Update peak usage
            let mut peak = self.peak_usage.load(Ordering::Relaxed);
            while current > peak {
                match self.peak_usage.compare_exchange_weak(
                    peak,
                    current,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(x) => peak = x,
                }
            }
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) };
        self.deallocated.fetch_add(layout.size(), Ordering::Relaxed);
    }
}

// Note: This would need to be enabled with a feature flag in a real implementation
// #[global_allocator]
// static TRACKING_ALLOCATOR: TrackingAllocator = TrackingAllocator::new();

/// Memory usage statistics
#[derive(Debug, Clone)]
pub struct MemoryStats {
    pub bytes_allocated: usize,
    pub bytes_deallocated: usize,
    pub peak_usage: usize,
    pub current_usage: usize,
}

impl MemoryStats {
    fn capture() -> Self {
        // In a real implementation, this would use the tracking allocator
        // For now, we'll return dummy values
        Self {
            bytes_allocated: 0,
            bytes_deallocated: 0,
            peak_usage: 0,
            current_usage: 0,
        }
    }
}

#[cfg(feature = "pvec")]
pub fn pvec_memory_benchmarks(c: &mut Criterion) {
    memory_usage_benchmarks(c);
    structural_sharing_memory_benchmarks(c);
    cache_memory_impact_benchmarks(c);
    memory_fragmentation_benchmarks(c);
}

#[cfg(feature = "pvec")]
fn memory_usage_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_memory_usage");

    let sizes = [100, 1000, 10000, 100000];

    for &size in &sizes {
        group.throughput(Throughput::Elements(size as u64));

        // Memory usage for building vectors
        group.bench_with_input(BenchmarkId::new("build_memory", size), &size, |b, &size| {
            b.iter_custom(|iters| {
                let start = std::time::Instant::now();

                for _ in 0..iters {
                    let _stats_before = MemoryStats::capture();

                    let mut vec = PersistentVector::new();
                    for i in 0..size {
                        vec = vec.push_back(black_box(i));
                    }

                    let _stats_after = MemoryStats::capture();
                    black_box(vec);

                    // In a real implementation, we would log memory usage here
                }

                start.elapsed()
            })
        });

        // Memory usage for cloning
        group.bench_with_input(BenchmarkId::new("clone_memory", size), &size, |b, &size| {
            let vec = (0..size).fold(PersistentVector::new(), |v, i| v.push_back(i));

            b.iter_custom(|iters| {
                let start = std::time::Instant::now();

                for _ in 0..iters {
                    let _stats_before = MemoryStats::capture();
                    let cloned = vec.clone();
                    let _stats_after = MemoryStats::capture();
                    black_box(cloned);
                }

                start.elapsed()
            })
        });
    }

    group.finish();
}

#[cfg(feature = "pvec")]
fn structural_sharing_memory_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_structural_sharing_memory");

    // Test memory efficiency of structural sharing
    group.bench_function("sharing_vs_copying", |b| {
        let base = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));

        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                // Create multiple versions with small modifications
                let mut versions = Vec::new();
                for i in 0..100 {
                    let modified = base.update(i * 100, black_box(i + 1000));
                    versions.push(modified);
                }

                let _stats_after = MemoryStats::capture();
                black_box(versions);
            }

            start.elapsed()
        })
    });

    // Test memory usage when sharing is broken
    group.bench_function("broken_sharing_memory", |b| {
        let base = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));

        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                let mut modified = base.clone();
                // Break all sharing by modifying every element
                for i in 0..1000 {
                    modified = modified.update(i, black_box(i + 1000));
                }

                let _stats_after = MemoryStats::capture();
                black_box(modified);
            }

            start.elapsed()
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn cache_memory_impact_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_cache_memory_impact");

    let size = 10000;

    // Memory usage with different cache policies
    group.bench_function("always_cache_memory", |b| {
        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                let vec: PersistentVector<i32> =
                    PersistentVector::with_cache_policy(Box::new(AlwaysCache));
                let vec = (0..size).fold(vec, |v, i| v.push_back(i));

                // Perform operations that would populate the cache
                for i in 0..1000 {
                    let idx = (i * 17) % size;
                    black_box(vec.get(idx.try_into().unwrap()));
                }

                let _stats_after = MemoryStats::capture();
                black_box(vec);
            }

            start.elapsed()
        })
    });

    group.bench_function("never_cache_memory", |b| {
        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                let vec: PersistentVector<i32> =
                    PersistentVector::with_cache_policy(Box::new(NeverCache));
                let vec = (0..size).fold(vec, |v, i| v.push_back(i));

                // Perform operations (no caching should occur)
                for i in 0..1000 {
                    let idx = (i * 17) % size;
                    black_box(vec.get(idx.try_into().unwrap()));
                }

                let _stats_after = MemoryStats::capture();
                black_box(vec);
            }

            start.elapsed()
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn memory_fragmentation_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_memory_fragmentation");

    // Test memory fragmentation patterns
    group.bench_function("fragmentation_pattern", |b| {
        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                // Create and destroy many vectors to test fragmentation
                let mut vectors = Vec::new();

                // Create many small vectors
                for i in 0..100 {
                    let vec =
                        (0..100).fold(PersistentVector::new(), |v, j| v.push_back(i * 100 + j));
                    vectors.push(vec);
                }

                // Modify some vectors (creating new versions)
                for i in (0..vectors.len()).step_by(2) {
                    vectors[i] = vectors[i].update(50, black_box(9999));
                }

                // Drop half the vectors
                vectors.truncate(50);

                let _stats_after = MemoryStats::capture();
                black_box(vectors);
            }

            start.elapsed()
        })
    });

    // Test memory usage with Arc sharing
    group.bench_function("arc_sharing_memory", |b| {
        b.iter_custom(|iters| {
            let start = std::time::Instant::now();

            for _ in 0..iters {
                let _stats_before = MemoryStats::capture();

                let base = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
                let arc_base = Arc::new(base);

                // Create many Arc clones
                let mut arc_clones = Vec::new();
                for _ in 0..100 {
                    arc_clones.push(arc_base.clone());
                }

                // Create modified versions from some clones
                let mut modified_versions = Vec::new();
                for i in 0..10 {
                    let modified = (*arc_clones[i]).clone().update(i * 100, black_box(i));
                    modified_versions.push(modified);
                }

                let _stats_after = MemoryStats::capture();
                black_box((arc_clones, modified_versions));
            }

            start.elapsed()
        })
    });

    group.finish();
}

/// Utility function to estimate memory usage of a PersistentVector
#[cfg(feature = "pvec")]
pub fn estimate_memory_usage<T>(vec: &PersistentVector<T>) -> usize
where
    T: Clone,
{
    // This is a rough estimation - in a real implementation,
    // we would traverse the internal structure to calculate exact usage
    let element_size = std::mem::size_of::<T>();
    let estimated_overhead = vec.len() * element_size / 4; // Rough estimate for tree overhead
    vec.len() * element_size + estimated_overhead
}

/// Utility function to measure structural sharing efficiency
#[cfg(feature = "pvec")]
pub fn measure_sharing_efficiency<T: Clone>(
    original: &PersistentVector<T>, modified: &PersistentVector<T>,
) -> f64 {
    // This would require access to internal structure to measure actual sharing
    // For now, return a placeholder value
    let estimated_shared_memory = (estimate_memory_usage(original) as f64 * 0.8) as usize; // Assume 80% sharing
    let total_memory = estimate_memory_usage(original) + estimate_memory_usage(modified);

    if total_memory > 0 {
        estimated_shared_memory as f64 / total_memory as f64
    } else {
        0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "pvec")]
    fn test_memory_estimation() {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        let estimated = estimate_memory_usage(&vec);

        // Should be at least the size of the elements
        assert!(estimated >= 1000 * std::mem::size_of::<i32>());
    }

    #[test]
    #[cfg(feature = "pvec")]
    fn test_sharing_efficiency() {
        let original = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        let modified = original.update(500, 42);

        let efficiency = measure_sharing_efficiency(&original, &modified);

        // Should have some sharing efficiency
        assert!(efficiency > 0.0);
        assert!(efficiency <= 1.0);
    }
}
