use rustica::datatypes::wrapper::memoizer::{Memoizer, MemoizerError};
use rustica::prelude::*;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

#[test]
fn test_memoizer_basic() {
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();
    let memoizer = Memoizer::new();

    // First call should compute the value
    let v1 = memoizer.get_or_compute((), |_| {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v1, 1);

    // Second call should use cache
    let v2 = memoizer.get_or_compute((), |_| unreachable!());
    assert_eq!(v2, 1);
    assert_eq!(*counter.lock().unwrap(), 1);

    // Clear cache and recompute
    memoizer.clear();
    let v3 = memoizer.get_or_compute((), |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v3, 2);
}

#[test]
fn test_memoizer_fn() {
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();
    let memoizer = Memoizer::new();

    // First call with value
    let v1 = memoizer.get_or_compute(5, |_| {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        10
    });
    assert_eq!(v1, 10);

    // Second call with same value uses cache
    let v2 = memoizer.get_or_compute(5, |_| unreachable!());
    assert_eq!(v2, 10);
    assert_eq!(*counter.lock().unwrap(), 1);

    // Call with new value
    let v3 = memoizer.get_or_compute(10, |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        20
    });
    assert_eq!(v3, 20);
    assert_eq!(*counter.lock().unwrap(), 2);

    // Clear cache and recompute for same value
    memoizer.clear();
    let v4 = memoizer.get_or_compute(10, |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        20
    });
    assert_eq!(v4, 20);
    assert_eq!(*counter.lock().unwrap(), 3);
}

#[test]
fn test_memoizer_with_capacity() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);

    // Insert first two items
    memo.insert(1, 10);
    memo.insert(2, 20);
    assert_eq!(memo.len(), 2);
    assert_eq!(memo.get(&1), Some(10));
    assert_eq!(memo.get(&2), Some(20));

    // Insert third item - should evict LRU (1)
    memo.insert(3, 30);
    assert_eq!(memo.len(), 2);
    assert_eq!(memo.get(&1), None); // Evicted
    assert_eq!(memo.get(&2), Some(20));
    assert_eq!(memo.get(&3), Some(30));
}

#[test]
fn test_memoizer_capacity_zero() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(0);

    // Should behave like unlimited cache
    memo.insert(1, 10);
    memo.insert(2, 20);
    memo.insert(3, 30);

    assert_eq!(memo.len(), 3);
    assert_eq!(memo.get(&1), Some(10));
    assert_eq!(memo.get(&2), Some(20));
    assert_eq!(memo.get(&3), Some(30));
}

#[test]
fn test_memoizer_get_with_lru_update() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    memo.get_or_compute(1, |k| k * 10);
    memo.get_or_compute(2, |k| k * 10);

    // Access key 1 to make it recently used
    assert_eq!(memo.get_with_lru_update(&1), Some(10));

    // Now key 2 is LRU, will be evicted next
    memo.get_or_compute(3, |k| k * 10);
    assert!(memo.contains_key(&1)); // Still present
    assert!(!memo.contains_key(&2)); // Evicted
}

#[test]
fn test_memoizer_insert_with_eviction_info() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    memo.insert(1, 10);
    memo.insert(2, 20);

    // Insert third key, causing eviction
    let (old, evicted_key, evicted_value) = memo.insert_with_eviction_info(3, 30);
    assert_eq!(old, None);
    assert_eq!(evicted_key, Some(1));
    assert_eq!(evicted_value, Some(10));

    // Update existing key
    let (old, evicted_key, evicted_value) = memo.insert_with_eviction_info(2, 200);
    assert_eq!(old, Some(20));
    assert_eq!(evicted_key, None);
    assert_eq!(evicted_value, None);
}

#[test]
fn test_memoizer_try_methods() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Test try_get_or_compute
    let result = memo.try_get_or_compute(1, |k| k * 10);
    assert_eq!(result.unwrap(), 10);

    // Test try_get
    assert_eq!(memo.try_get(&1).unwrap(), Some(10));

    // Test try_get_with_lru_update
    assert_eq!(memo.try_get_with_lru_update(&1).unwrap(), Some(10));

    // Test try_insert
    assert_eq!(memo.try_insert(2, 20).unwrap(), None);
    assert_eq!(memo.try_insert(2, 200).unwrap(), Some(20));

    // Test try_insert_with_eviction_info
    let (old, evicted_key, evicted_value) = memo.try_insert_with_eviction_info(3, 30).unwrap();
    assert_eq!(old, None);
    assert_eq!(evicted_key, None);
    assert_eq!(evicted_value, None);
}

#[test]
fn test_memoizer_get_or_try_compute() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Successful computation
    let result: Result<i32, String> = memo.get_or_try_compute(1, |k| Ok(k * 10));
    assert_eq!(result.unwrap(), 10);

    // Failed computation (not cached)
    let result: Result<i32, String> =
        memo.get_or_try_compute(2, |_| Err("computation failed".to_string()));
    assert!(result.is_err());
    assert!(!memo.contains_key(&2)); // Error not cached

    // Successful computation for same key
    let result: Result<i32, String> = memo.get_or_try_compute(2, |k| Ok(k * 20));
    assert_eq!(result.unwrap(), 40);
}

#[test]
fn test_memoizer_get_or_compute_optimistic() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Basic optimistic computation
    let v1 = memo.get_or_compute_optimistic(1, |k| k * 10);
    assert_eq!(v1, 10);

    // Should use cache
    let v2 = memo.get_or_compute_optimistic(1, |_| 999);
    assert_eq!(v2, 10);

    // New key
    let v3 = memo.get_or_compute_optimistic(2, |k| k * 20);
    assert_eq!(v3, 40);
}

#[test]
fn test_memoizer_try_get_or_compute_optimistic() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Test optimistic computation
    let result = memo.try_get_or_compute_optimistic(1, |k| k * 10);
    assert_eq!(result.unwrap(), 10);

    // Should use cache
    let result = memo.try_get_or_compute_optimistic(1, |_| 999);
    assert_eq!(result.unwrap(), 10);
}

#[test]
fn test_memoizer_touch() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    memo.get_or_compute(1, |k| k * 10);
    memo.get_or_compute(2, |k| k * 10);

    // Touch key 1 to make it recently used
    assert!(memo.touch(&1));

    // Now key 2 is LRU, will be evicted next
    memo.get_or_compute(3, |k| k * 10);
    assert!(memo.contains_key(&1)); // Still present
    assert!(!memo.contains_key(&2)); // Evicted

    // Touch non-existent key
    assert!(!memo.touch(&99));
}

#[test]
fn test_memoizer_try_touch() {
    let memo: Memoizer<i32, i32> = Memoizer::new();
    memo.insert(1, 10);

    assert!(memo.try_touch(&1).unwrap());
    assert!(!memo.try_touch(&2).unwrap());
}

#[test]
fn test_memoizer_stats() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Initial stats
    let stats = memo.stats();
    assert_eq!(stats.hits, 0);
    assert_eq!(stats.misses, 0);
    assert_eq!(stats.evictions, 0);
    assert_eq!(stats.hit_rate(), 0.0);

    // First computation - miss
    memo.get_or_compute(1, |k| k * 10);
    let stats = memo.stats();
    assert_eq!(stats.hits, 0);
    assert_eq!(stats.misses, 1);
    assert_eq!(stats.evictions, 0);
    assert_eq!(stats.hit_rate(), 0.0);

    // Second access via get_or_compute - hit (get() uses peek which doesn't count as hit)
    memo.get_or_compute(1, |_| unreachable!());
    let stats = memo.stats();
    assert_eq!(stats.hits, 1);
    assert_eq!(stats.misses, 1);
    assert_eq!(stats.evictions, 0);
    assert_eq!(stats.hit_rate(), 0.5);

    // Reset stats
    memo.reset_stats();
    let stats = memo.stats();
    assert_eq!(stats.hits, 0);
    assert_eq!(stats.misses, 0);
    assert_eq!(stats.evictions, 0);
    assert_eq!(stats.hit_rate(), 0.0);
}

#[test]
fn test_memoizer_max_capacity() {
    let unlimited: Memoizer<i32, i32> = Memoizer::new();
    assert_eq!(unlimited.max_capacity(), None);

    let bounded: Memoizer<i32, i32> = Memoizer::with_capacity(100);
    assert_eq!(bounded.max_capacity(), Some(100));

    let zero_capacity: Memoizer<i32, i32> = Memoizer::with_capacity(0);
    assert_eq!(zero_capacity.max_capacity(), Some(0)); // 0 means disabled cache
}

#[test]
fn test_memoizer_len_and_is_empty() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    assert_eq!(memo.len(), 0);
    assert!(memo.is_empty());

    memo.insert(1, 10);
    assert_eq!(memo.len(), 1);
    assert!(!memo.is_empty());

    memo.clear();
    assert_eq!(memo.len(), 0);
    assert!(memo.is_empty());
}

#[test]
fn test_memoizer_try_len_and_try_is_empty() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    assert_eq!(memo.try_len().unwrap(), 0);
    assert!(memo.try_is_empty().unwrap());

    memo.insert(1, 10);
    assert_eq!(memo.try_len().unwrap(), 1);
    assert!(!memo.try_is_empty().unwrap());
}

#[test]
fn test_memoizer_contains_key() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    assert!(!memo.contains_key(&1));

    memo.insert(1, 10);
    assert!(memo.contains_key(&1));
    assert!(!memo.contains_key(&2));
}

#[test]
fn test_memoizer_try_contains_key() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    assert!(!memo.try_contains_key(&1).unwrap());

    memo.insert(1, 10);
    assert!(memo.try_contains_key(&1).unwrap());
    assert!(!memo.try_contains_key(&2).unwrap());
}

#[test]
fn test_memoizer_remove() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.insert(1, 10);
    memo.insert(2, 20);

    assert_eq!(memo.remove(&1), Some(10));
    assert_eq!(memo.remove(&1), None);
    assert_eq!(memo.len(), 1);
    assert!(!memo.contains_key(&1));
    assert!(memo.contains_key(&2));
}

#[test]
fn test_memoizer_try_remove() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.insert(1, 10);

    assert_eq!(memo.try_remove(&1).unwrap(), Some(10));
    assert_eq!(memo.try_remove(&1).unwrap(), None);
}

#[test]
fn test_memoizer_reserve_and_capacity() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.reserve(100);
    assert!(memo.capacity() >= 100);

    memo.insert(1, 10);
    memo.insert(2, 20);
    memo.insert(3, 30);

    memo.shrink_to_fit();
    // After shrinking, capacity should be just enough for current entries
    assert!(memo.capacity() >= 3);
}

#[test]
fn test_memoizer_try_reserve_and_try_capacity() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.try_reserve(100).unwrap();
    assert!(memo.try_capacity().unwrap() >= 100);
}

#[test]
fn test_memoizer_keys_and_values() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.insert(1, 10);
    memo.insert(2, 20);
    memo.insert(3, 30);

    let mut keys = memo.keys();
    keys.sort();
    assert_eq!(keys, vec![1, 2, 3]);

    let mut values = memo.values();
    values.sort();
    assert_eq!(values, vec![10, 20, 30]);
}

#[test]
fn test_memoizer_try_keys_and_try_values() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.insert(1, 10);
    memo.insert(2, 20);

    let keys = memo.try_keys().unwrap();
    assert!(keys.contains(&1));
    assert!(keys.contains(&2));

    let values = memo.try_values().unwrap();
    assert!(values.contains(&10));
    assert!(values.contains(&20));
}

#[test]
fn test_memoizer_try_clear() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    memo.insert(1, 10);
    memo.insert(2, 20);

    memo.try_clear().unwrap();
    assert_eq!(memo.len(), 0);
    assert!(memo.is_empty());
}

#[test]
fn test_memoizer_default() {
    let memo: Memoizer<i32, i32> = Memoizer::default();

    // Should work like new()
    memo.insert(1, 10);
    assert_eq!(memo.get(&1), Some(10));
}

#[test]
fn single_thread_memoization() {
    let memo: Memoizer<u32, u32> = Memoizer::new();
    let result = memo.get_or_compute(5, |x| x * 2);
    assert_eq!(result, 10);
    // Should hit cache
    let again = memo.get_or_compute(5, |_| 999);
    assert_eq!(again, 10);
}

#[test]
fn multi_threaded_memoization() {
    let memo = Arc::new(Memoizer::new());
    let handles: Vec<_> = (0..8)
        .map(|i| {
            let memo = memo.clone();
            thread::spawn(move || memo.get_or_compute(i % 3, |x| x * 10))
        })
        .collect();
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for &v in &[0, 10, 20] {
        assert!(results.contains(&v));
    }
}

#[test]
fn clear_cache() {
    let memo: Memoizer<u32, u32> = Memoizer::new();
    memo.get_or_compute(1, |x| x + 1);
    memo.clear();
    let v = memo.get_or_compute(1, |_| 42);
    assert_eq!(v, 42);
}

#[test]
fn test_concurrent_access() {
    let memo = Arc::new(Memoizer::with_capacity(10));
    let mut handles = vec![];

    // Spawn multiple threads that access and update the cache
    for i in 0..10 {
        let memo = memo.clone();
        let handle = thread::spawn(move || {
            for j in 0..100 {
                let key = i * 10 + j;
                memo.get_or_compute(key, |k| k * 2);

                // Occasionally access existing keys
                if j % 10 == 0 && j > 0 {
                    memo.get(&(key - 1));
                }
            }
        });
        handles.push(handle);
    }

    // Wait for all threads to complete
    for handle in handles {
        handle.join().unwrap();
    }

    // Verify cache has some entries
    assert!(!memo.is_empty());
    assert!(memo.len() <= 10); // Should not exceed capacity
}

#[test]
fn test_lru_eviction_order() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(3);

    // Insert 3 items
    memo.insert(1, 10);
    memo.insert(2, 20);
    memo.insert(3, 30);

    // Access 1 to make it MRU
    memo.get_with_lru_update(&1);

    // Insert 4th item, should evict 2 (LRU)
    memo.insert(4, 40);

    assert_eq!(memo.get(&1), Some(10)); // Still present (was accessed)
    assert_eq!(memo.get(&2), None); // Evicted
    assert_eq!(memo.get(&3), Some(30)); // Still present
    assert_eq!(memo.get(&4), Some(40)); // New item
}

#[test]
fn test_memoizer_error_handling() {
    // Test that MemoizerError implements required traits
    let error = MemoizerError {
        message: "test error".to_string(),
    };

    assert_eq!(error.to_string(), "MemoizerError: test error");

    // Test Debug
    let debug_str = format!("{:?}", error);
    assert!(debug_str.contains("MemoizerError"));
    assert!(debug_str.contains("test error"));
}

#[test]
fn test_memoizer_complex_key_types() {
    // Test with complex key types
    let memo: Memoizer<Vec<i32>, String> = Memoizer::new();

    let key1 = vec![1, 2, 3];
    let key2 = vec![4, 5, 6];

    memo.get_or_compute(key1.clone(), |_| "first".to_string());
    memo.get_or_compute(key2.clone(), |_| "second".to_string());

    assert_eq!(memo.get(&key1), Some("first".to_string()));
    assert_eq!(memo.get(&key2), Some("second".to_string()));
}

#[test]
fn test_memoizer_arc_values() {
    // Test with Arc values
    let memo: Memoizer<i32, Arc<String>> = Memoizer::new();

    let value = Arc::new("test".to_string());
    memo.insert(1, value.clone());

    let retrieved = memo.get(&1).unwrap();
    assert!(Arc::ptr_eq(&value, &retrieved)); // Same Arc instance
}

#[test]
fn test_memoizer_string_keys() {
    let memo: Memoizer<String, i32> = Memoizer::new();

    memo.get_or_compute("hello".to_string(), |s| s.len() as i32);
    memo.get_or_compute("world".to_string(), |s| s.len() as i32);

    assert_eq!(memo.get(&"hello".to_string()), Some(5));
    assert_eq!(memo.get(&"world".to_string()), Some(5));
}

#[test]
fn test_memoizer_statistics_accuracy() {
    let memo: Memoizer<i32, i32> = Memoizer::new();

    // Perform various operations - all misses
    for i in 0..10 {
        memo.get_or_compute(i, |x| x * 2);
    }

    // Access some existing keys via get_or_compute - these are hits
    // Note: get() uses peek() which doesn't update hit stats
    for i in 0..5 {
        memo.get_or_compute(i, |_| unreachable!());
    }

    let stats = memo.stats();
    assert_eq!(stats.misses, 10);
    assert_eq!(stats.hits, 5);
    assert_eq!(stats.total_accesses(), 15);
    assert!((stats.hit_rate() - 0.3333).abs() < 0.01);
}

#[test]
fn test_memoizer_eviction_statistics() {
    let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);

    // Fill capacity
    memo.insert(1, 10);
    memo.insert(2, 20);

    // Cause eviction
    memo.insert(3, 30);
    memo.insert(4, 40);

    let stats = memo.stats();
    assert_eq!(stats.evictions, 2);
}

#[cfg(feature = "serde")]
#[test]
fn test_memoizer_serde() {
    let memo: Memoizer<i32, i32> = Memoizer::new();
    memo.insert(1, 10);
    memo.insert(2, 20);

    // Note: Memoizer itself doesn't implement serde due to RwLock
    // This test documents this limitation
    // If needed, users should extract the data and serialize that instead
}

// Test for the race condition fix in get_or_compute_optimistic
#[test]
fn test_get_or_compute_optimistic_race_condition() {
    use std::sync::atomic::{AtomicU32, Ordering};

    let memo = Arc::new(Memoizer::new());
    let compute_count = Arc::new(AtomicU32::new(0));
    let mut handles = vec![];

    // Spawn multiple threads that try to compute the same key
    // Note: optimistic approach allows multiple computations but ensures
    // all threads return the same cached value after the first insertion
    for _ in 0..10 {
        let memo = memo.clone();
        let compute_count = compute_count.clone();
        let handle = thread::spawn(move || {
            memo.get_or_compute_optimistic(42, |_| {
                compute_count.fetch_add(1, Ordering::Relaxed);
                thread::sleep(Duration::from_millis(10));
                100
            })
        });
        handles.push(handle);
    }

    // Collect results
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All results should be the same value
    for &result in &results {
        assert_eq!(result, 100);
    }

    // Optimistic approach may compute multiple times, but cache is consistent
    // The important thing is that the cached value is correct
    assert!(compute_count.load(Ordering::Relaxed) >= 1);

    // Cache should contain the computed value
    assert_eq!(memo.get(&42), Some(100));
}
