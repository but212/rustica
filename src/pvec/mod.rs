//! Persistent vector implementation using RRB (Relaxed Radix Balanced) trees.
//!
//! This module provides a persistent, immutable vector data structure that supports
//! efficient operations for insertion, deletion, and random access. The implementation
//! uses RRB trees which maintain logarithmic performance characteristics while
//! supporting efficient concatenation and splitting operations.
//!
//! # Key Features
//!
//! - **Persistence**: All operations return new vectors, leaving the original unchanged
//! - **Structural Sharing**: Modified vectors share structure with originals, minimizing memory usage
//! - **Adaptive Storage**: Small vectors (≤64 elements) use inline storage for optimal performance
//! - **Efficient Operations**: O(log n) for most operations including random access, update, and split
//! - **Bounded Branches**: Every RRB branch contains at most 32 children, including after concatenation
//!
//! # When to Use
//!
//! Use `PersistentVector` when you need:
//! - Immutable data structures with efficient updates
//! - Version history or undo/redo functionality
//! - Safe sharing across threads without locks
//! - Functional programming patterns
//!
//! For mutable use cases where persistence isn't needed, prefer `Vec<T>`.
//!
//! # Error Handling Policy
//!
//! This module follows a dual approach to error handling:
//!
//! - **Total functions** (e.g., `update`, `get`): Return a default value or `Option`
//!   when operations cannot complete. This supports functional programming patterns
//!   where operations should always succeed.
//!
//! - **Fallible functions** (e.g., `try_update`, `try_get`): Return `Result` with
//!   detailed error information via `PVecError`.
//!
//! | Operation | Total Version | Fallible Version |
//! |-----------|---------------|------------------|
//! | Get element | `get()` → `Option<&T>` | `try_get()` → `Result<&T, PVecError>` |
//! | Update element | `update()` → `Self` (clone on error) | `try_update()` → `Result<Self, PVecError>` |
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::{PersistentVector, pvec};
//!
//! // Create a new empty vector
//! let vec: PersistentVector<i32> = PersistentVector::new();
//!
//! // Use the convenience macro
//! let vec = pvec![1, 2, 3, 4, 5];
//!
//! // Add elements
//! let vec = vec.push_back(6).push_front(0);
//!
//! // Access elements
//! assert_eq!(vec.get(0), Some(&0));
//! assert_eq!(vec.get(6), Some(&6));
//! ```

pub mod core;
pub mod error;
pub mod iter;
pub(crate) mod node;
pub mod traits;
pub(crate) mod tree;

pub use core::PersistentVector;
pub use error::PVecError;
pub use iter::{PersistentVectorIntoIter, PersistentVectorIter};

/// Convenience macro for creating persistent vectors.
///
/// # Examples
///
/// ```
/// use rustica::pvec::pvec;
/// use rustica::pvec::PersistentVector;
///
/// // Empty vector
/// let empty: PersistentVector<i32> = pvec![];
///
/// // Vector with elements
/// let vec = pvec![1, 2, 3, 4, 5];
/// ```
#[macro_export]
macro_rules! pvec {
    () => { $crate::pvec::PersistentVector::new() };
    ($($x:expr),+ $(,)?) => {
        $crate::pvec::PersistentVector::from_iter([$($x),+])
    };
}

pub use pvec;

#[cfg(test)]
mod tests {
    use super::PersistentVector;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[test]
    fn test_pvec_lifecycle_and_persistence() {
        let empty: PersistentVector<i32> = PersistentVector::new();
        let single = PersistentVector::unit(42);
        let mac = crate::pvec![1, 2, 3];
        assert!(empty.is_empty());
        assert_eq!(single.len(), 1);
        assert_eq!(mac.get(2), Some(&3));

        let v1 = crate::pvec![10, 20];
        let v2 = v1.push_back(30);
        let v3 = v1.push_back(40);
        assert_eq!(v1.to_vec(), vec![10, 20]);
        assert_eq!(v2.to_vec(), vec![10, 20, 30]);
        assert_eq!(v3.to_vec(), vec![10, 20, 40]);

        let std_vec: Vec<i32> = v1.clone().into();
        let from_std: PersistentVector<i32> = std_vec.into();
        assert_eq!(v1, from_std);
    }

    #[test]
    fn unequal_height_concat_preserves_operand_order() {
        let short = PersistentVector::unit(0);
        let long: PersistentVector<usize> = (1..130).collect();
        assert_eq!(short.concat(&long).to_vec(), (0..130).collect::<Vec<_>>());
        assert_eq!(
            long.concat(&short).to_vec(),
            (1..130).chain([0]).collect::<Vec<_>>()
        );
    }

    #[test]
    fn pop_back_handles_head_and_tree_storage() {
        for length in [65, 129] {
            let mut vector = PersistentVector::new();
            for value in 0..length {
                vector = vector.push_front(value);
            }

            let mut expected: Vec<_> = (0..length).rev().collect();
            for _ in 0..length {
                let (without_last, last) = vector.pop_back().expect("non-empty vector");
                assert_eq!(last, expected.pop().expect("expected value"));
                assert_eq!(without_last.to_vec(), expected);
                vector = without_last;
            }
            assert!(vector.pop_back().is_none());
        }
    }

    #[test]
    fn test_pvec_element_access_and_updates() {
        let vec = crate::pvec![1, 2, 3];
        assert_eq!(vec.first(), Some(&1));
        assert_eq!(vec.last(), Some(&3));
        assert_eq!(vec[1], 2);

        let updated = vec.update(1, 20).update(10, 999);
        assert_eq!(updated[1], 20);
        assert_eq!(updated.len(), 3);

        let (vec2, val) = vec.pop_back().expect("Should pop 3");
        assert_eq!(val, 3);
        assert_eq!(vec2.len(), 2);
        assert!(PersistentVector::<i32>::new().pop_back().is_none());
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_pvec_index_panic() {
        let _ = crate::pvec![1, 2][10];
    }

    #[test]
    fn test_pvec_transformations() {
        let vec = crate::pvec![1, 2, 2, 3, 4];
        let processed = vec.map(|x| x * 10).filter(|&x| x > 20).sorted();
        assert_eq!(processed.to_vec(), vec![30, 40]);

        let combined = vec.concat(&crate::pvec![5, 6]);
        assert_eq!(combined.len(), 7);
        assert_eq!(vec.dedup().len(), 4);
        assert_eq!(vec.insert(1, 99).get(1), Some(&99));

        let filtered = vec.filter_map(|&x| if x % 2 == 0 { Some(x) } else { None });
        assert_eq!(filtered.to_vec(), vec![2, 2, 4]);
    }

    #[test]
    fn test_pvec_iteration() {
        let vec = crate::pvec![1, 2, 3];
        assert_eq!(vec.iter().sum::<i32>(), 6);

        let collected: Vec<i32> = vec.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);

        let from_it: PersistentVector<_> = (0..5).collect();
        assert_eq!(from_it.len(), 5);
    }

    #[test]
    fn test_pvec_tree_integrity() {
        let mut vec: PersistentVector<i32> = PersistentVector::new();
        for i in 0..100 {
            vec = vec.push_back(i);
            assert_eq!(vec.get(i as usize), Some(&i));
        }

        for &idx in &[0usize, 31, 32, 63, 64, 99] {
            assert_eq!(vec.get(idx), Some(&(idx as i32)));
        }

        let updated = vec.update(31, 310).update(32, 320);
        assert_eq!(updated.get(31), Some(&310));
        assert_eq!(vec.get(31), Some(&31));

        let n = 10_000usize;
        let large_vec: PersistentVector<i32> = (0..n as i32).collect();
        assert_eq!(large_vec.len(), n);
        assert_eq!(large_vec.get(n - 1), Some(&((n - 1) as i32)));

        let (left, right) = large_vec.split_at(n / 2);
        assert_eq!(left.concat(&right).to_vec(), large_vec.to_vec());
    }

    #[test]
    fn pvec_owned_construction_and_conversion_do_not_require_clone() {
        struct NoClone(u32);

        let vector: PersistentVector<NoClone> = (0..65).map(NoClone).collect();
        assert_eq!(vector.len(), 65);
        assert_eq!(vector.get(64).unwrap().0, 64);
        let _from_vec: PersistentVector<NoClone> = vec![NoClone(1), NoClone(2)].into();
    }

    #[test]
    fn test_pvec_remove_comprehensive() {
        // 1. Empty vector
        let empty: PersistentVector<i32> = PersistentVector::new();
        assert_eq!(empty.remove(0), None);
        assert_eq!(empty.remove(10), None);

        // 2. Out of bounds
        let v3 = crate::pvec![1, 2, 3];
        assert_eq!(v3.remove(3), None);
        assert_eq!(v3.remove(100), None);

        // 3. Single element
        let single = PersistentVector::unit(42);
        let removed_single = single.remove(0).expect("should succeed");
        assert_eq!(removed_single.len(), 0);
        assert_eq!(removed_single.to_vec(), Vec::<i32>::new());

        // 4. Remove first, mid, last
        let v5 = crate::pvec![10, 20, 30, 40, 50];
        assert_eq!(v5.remove(0).unwrap().to_vec(), vec![20, 30, 40, 50]);
        assert_eq!(v5.remove(2).unwrap().to_vec(), vec![10, 20, 40, 50]);
        assert_eq!(v5.remove(4).unwrap().to_vec(), vec![10, 20, 30, 40]);

        // 5. Large vector (>64 elements, tree/branch boundary)
        let large: PersistentVector<i32> = (0..100).collect();
        assert_eq!(
            large.remove(0).unwrap().to_vec(),
            (1..100).collect::<Vec<_>>()
        );
        assert_eq!(
            large.remove(99).unwrap().to_vec(),
            (0..99).collect::<Vec<_>>()
        );

        let remove_mid = large.remove(50).unwrap();
        assert_eq!(remove_mid.len(), 99);
        let mut expected: Vec<i32> = (0..100).collect();
        expected.remove(50);
        assert_eq!(remove_mid.to_vec(), expected);
    }

    #[test]
    fn split_after_insert_preserves_values_and_lengths() {
        let vector: PersistentVector<i32> = (0..83).collect();
        let inserted = vector.insert(38, 999);
        let expected: Vec<i32> = (0..38).chain(std::iter::once(999)).chain(38..83).collect();

        let (left, right) = inserted.split_at(42);
        assert_eq!(left.len(), 42);
        assert_eq!(right.len(), 42);
        assert_eq!(left.to_vec(), expected[..42]);
        assert_eq!(right.to_vec(), expected[42..]);
        assert_eq!(left.concat(&right).to_vec(), expected);

        let removed = inserted
            .remove(38)
            .expect("inserted value should be removable");
        assert_eq!(removed.to_vec(), (0..83).collect::<Vec<_>>());
    }

    #[test]
    fn representation_and_history_do_not_affect_value_semantics() {
        let collected: PersistentVector<i32> = (0..100).collect();
        let pushed = (0..100).fold(PersistentVector::new(), |vector, value| {
            vector.push_back(value)
        });
        let rebuilt = collected.split_at(64).0.concat(&collected.split_at(64).1);

        assert_eq!(collected, pushed);
        assert_eq!(collected, rebuilt);
        assert_eq!(collected.cmp(&pushed), std::cmp::Ordering::Equal);

        let hash = |vector: &PersistentVector<i32>| {
            let mut hasher = DefaultHasher::new();
            vector.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(hash(&collected), hash(&pushed));
        assert_eq!(hash(&collected), hash(&rebuilt));
    }

    #[test]
    fn inline_tree_boundary_lengths_follow_the_representation() {
        for len in [0usize, 1, 63, 64, 65, 127] {
            let vector: PersistentVector<usize> = (0..len).collect();
            assert_eq!(vector.len(), len);
            assert_eq!(vector.iter().count(), len);

            let (left, right) = vector.split_at(len / 2);
            assert_eq!(left.len() + right.len(), len);
            assert_eq!(left.concat(&right), vector);
        }
    }
}
