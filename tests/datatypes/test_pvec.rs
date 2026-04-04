use rustica::pvec;
use rustica::pvec::PersistentVector;

// --- Lifecycle and Persistence ---

#[test]
fn test_pvec_lifecycle_and_persistence() {
    // 1. Diverse Creations (new, unit, macro)
    let empty: PersistentVector<i32> = PersistentVector::new();
    let single = PersistentVector::unit(42);
    let mac = pvec![1, 2, 3];
    assert!(empty.is_empty());
    assert_eq!(single.len(), 1);
    assert_eq!(mac.get(2), Some(&3));

    // 2. Verified Persistence (v1 remains unchanged)
    let v1 = pvec![10, 20];
    let v2 = v1.push_back(30);
    let v3 = v1.push_back(40);
    assert_eq!(v1.to_vec(), vec![10, 20]);
    assert_eq!(v2.to_vec(), vec![10, 20, 30]);
    assert_eq!(v3.to_vec(), vec![10, 20, 40]);

    // 3. Trait Conversions
    let std_vec: Vec<i32> = v1.clone().into();
    let from_std: PersistentVector<i32> = std_vec.into();
    assert_eq!(v1, from_std);
}

// --- Core Operations & Access ---

#[test]
fn test_pvec_element_access_and_updates() {
    let vec = pvec![1, 2, 3];

    // 1. Sequential and Random access
    assert_eq!(vec.first(), Some(&1));
    assert_eq!(vec.last(), Some(&3));
    assert_eq!(vec[1], 2);

    // 2. Updates and Boundary checks
    let updated = vec.update(1, 20).update(10, 999); // Out of bounds update should be safe/no-op
    assert_eq!(updated[1], 20);
    assert_eq!(updated.len(), 3);

    // 3. Stack-like behavior (Pop)
    let (vec2, val) = vec.pop_back().expect("Should pop 3");
    assert_eq!(val, 3);
    assert_eq!(vec2.len(), 2);
    assert!(PersistentVector::<i32>::new().pop_back().is_none());
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn test_pvec_index_panic() {
    let _ = pvec![1, 2][10];
}

// --- Transformations & Pipeline ---

#[test]
fn test_pvec_transformations() {
    let vec = pvec![1, 2, 2, 3, 4];

    // 1. Common Pipeline (Map, Filter, Sorted)
    let processed = vec.map(|x| x * 10).filter(|&x| x > 20).sorted();
    assert_eq!(processed.to_vec(), vec![30, 40]);

    // 2. Advanced Utilities (Concat, Dedup, Insert)
    let combined = vec.concat(&pvec![5, 6]);
    assert_eq!(combined.len(), 7);
    assert_eq!(vec.dedup().len(), 4);
    assert_eq!(vec.insert(1, 99).get(1), Some(&99));

    // 3. Fallible Mapping
    let filtered = vec.filter_map(|&x| if x % 2 == 0 { Some(x) } else { None });
    assert_eq!(filtered.to_vec(), vec![2, 2, 4]);
}

// --- Iteration ---

#[test]
fn test_pvec_iteration() {
    let vec = pvec![1, 2, 3];

    // Reference iteration
    assert_eq!(vec.iter().sum::<i32>(), 6);

    // Consuming iteration
    let collected: Vec<i32> = vec.clone().into_iter().collect();
    assert_eq!(collected, vec![1, 2, 3]);

    // Construct from iterator
    let from_it: PersistentVector<_> = (0..5).collect();
    assert_eq!(from_it.len(), 5);
}

// --- Tree Integrity & Large Data ---

#[test]
fn test_pvec_tree_integrity() {
    // 1. Boundary crossing (Trie depth increases around 32/64 elements)
    let mut vec: PersistentVector<i32> = PersistentVector::new();
    for i in 0..100 {
        vec = vec.push_back(i);
        assert_eq!(vec.get(i as usize), Some(&i));
    }

    // Verify key boundaries (0, 31, 32, 63, 64)
    for &idx in &[0usize, 31, 32, 63, 64, 99] {
        assert_eq!(vec.get(idx), Some(&(idx as i32)));
    }

    // 2. Persistence after boundary updates
    let updated = vec.update(31, 310).update(32, 320);
    assert_eq!(updated.get(31), Some(&310));
    assert_eq!(vec.get(31), Some(&31)); // original preserved

    // 3. Large scale integrity and split/concat
    let n = 10_000usize;
    let large_vec: PersistentVector<i32> = (0..n as i32).collect();
    assert_eq!(large_vec.len(), n);
    assert_eq!(large_vec.get(n - 1), Some(&((n - 1) as i32)));

    let (left, right) = large_vec.split_at(n / 2);
    assert_eq!(left.concat(&right).to_vec(), large_vec.to_vec());
}
