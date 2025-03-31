
//! # Persistent Vector
//! 
//! A persistent vector implementation using Relaxed Radix Balanced Trees.
//! 
//! This data structure provides efficient immutable operations while
//! maintaining structural sharing between versions. This makes it ideal
//! for functional programming patterns and concurrent applications where
//! immutable data structures are preferred.
//! 
//! ## Performance Characteristics
//! 
//! - Access: O(log n)
//! - Insert/Update: O(log n)
//! - Push/Pop: O(1) amortized
//! - Concatenation: O(log n)
//! 
//! ## Implementation Details
//! 
//! The vector uses a combination of strategies for optimal performance:
//! 
//! 1. Small vectors use an optimized representation for better memory usage
//! 2. Larger vectors use a tree structure with a fixed branching factor
//! 3. A flexible memory management system to reduce allocation overhead
//! 4. Intelligent caching for faster sequential access

pub mod chunk;
pub mod memory;
pub mod node;
pub mod tree;
pub mod vector;
pub mod iterator;
pub mod cache;

// Re-export the main types
pub use self::vector::PersistentVector;
pub use self::memory::MemoryManager;
pub use self::iterator::{Iter, IntoIter, ChunksIter, SortedIter};

// Create a convenience macro for creating vectors
#[macro_export]
macro_rules! pvec {
    () => { $crate::pvec::PersistentVector::new() };
    
    ($($x:expr),*) => {{
        let mut v = $crate::pvec::PersistentVector::new();
        $(
            v = v.push_back($x);
        )*
        v
    }};
    
    ($($x:expr,)*) => { pvec![$($x),*] };
}