use rustica::datatypes::wrapper::memoizer::{Memoizer, MemoizerError};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

#[test]
fn test_memoizer_core_and_eviction() {
    // 1. Basic Caching and Clearing
    let memo = Memoizer::with_capacity(2);
    let counter = Arc::new(Mutex::new(0));
    let compute = |k: &i32| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        k * 10
    };

    assert_eq!(memo.get_or_compute(1, compute), 10);
    assert_eq!(memo.get_or_compute(1, |_| unreachable!()), 10); // Cache hit
    assert_eq!(*counter.lock().unwrap(), 1);

    // 2. LRU Eviction Logic
    memo.get_or_compute(2, compute); // [1, 2]
    memo.get_or_compute(3, compute); // [2, 3], key 1 evicted
    assert!(!memo.contains_key(&1));
    assert!(memo.contains_key(&2) && memo.contains_key(&3));

    // 3. LRU Update via access (get/touch)
    memo.touch(&2); // 2 is MRU
    memo.get_or_compute(4, compute); // [2, 4], key 3 evicted instead of 2
    assert!(memo.contains_key(&2));
    assert!(!memo.contains_key(&3));

    // 4. Manual clearing
    memo.clear();
    assert!(memo.is_empty());
}

#[test]
fn test_memoizer_concurrency_and_race_conditions() {
    let memo = Arc::new(Memoizer::new());
    let mut handles = vec![];

    // 1. Multi-threaded access and shared state
    for i in 0..8 {
        let memo = memo.clone();
        handles.push(thread::spawn(move || {
            for j in 0..50 {
                let key = i * 10 + j;
                memo.get_or_compute(key, |k| k * 2);
            }
        }));
    }

    // 2. Optimistic computation (Race condition fix verification)
    use std::sync::atomic::{AtomicU32, Ordering};
    let compute_count = Arc::new(AtomicU32::new(0));
    for _ in 0..10 {
        let memo = memo.clone();
        let count = compute_count.clone();
        handles.push(thread::spawn(move || {
            memo.get_or_compute_optimistic(999, |_| {
                count.fetch_add(1, Ordering::Relaxed);
                thread::sleep(Duration::from_millis(10));
                1000
            });
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    assert_eq!(memo.get_or_compute(999, |_| 0), 1000);
}

#[test]
fn test_memoizer_collection_api_and_stats() {
    let memo = Memoizer::new();
    memo.insert(1, 10);
    memo.insert(2, 20);

    // Standard map-like helpers
    assert_eq!(memo.len(), 2);
    assert_eq!(memo.remove(&1), Some(10));
    assert_eq!(memo.keys(), vec![2]);
    assert_eq!(memo.values(), vec![20]);

    // Capacity and Stats
    assert!(memo.capacity() >= 1);
    let stats = memo.stats();
    assert_eq!(stats.misses, 0); // insert doesn't count as miss
    memo.get_or_compute(2, |_| 0); // hit
    memo.get_or_compute(3, |_| 0); // miss
    assert_eq!(memo.stats().hits, 1);
    assert_eq!(memo.stats().misses, 1);
}

#[test]
fn test_memoizer_resilience_and_errors() {
    let memo = Memoizer::new();

    // 1. Fallible computation (not cached on Err)
    let err_res: Result<i32, &str> = memo.get_or_try_compute(1, |_| Err("fail"));
    assert!(err_res.is_err());
    assert!(!memo.contains_key(&1));

    // 2. Try variants (Result-returning API)
    assert!(memo.try_insert(1, 10).is_ok());
    assert_eq!(memo.try_get(&1).unwrap(), Some(10));
    assert!(memo.try_touch(&1).unwrap());

    // 3. Error trait implementation
    let err = MemoizerError {
        message: "msg".to_string(),
    };
    assert!(format!("{:?}", err).contains("MemoizerError"));
}

#[test]
fn test_memoizer_complex_types() {
    // Testing with Arc and Vec keys/values
    let memo: Memoizer<Vec<i32>, Arc<String>> = Memoizer::new();
    let key = vec![1, 2, 3];
    let val = Arc::new("test".to_string());

    memo.insert(key.clone(), val.clone());
    let retrieved = memo.get(&key).unwrap();
    assert!(Arc::ptr_eq(&val, &retrieved));
}
