//! RRB Tree Implementation
//!
//! This module provides the core implementation of the Relaxed Radix Balanced Tree
//! that powers the persistent vector.

use crate::pvec::chunk::{Chunk, CHUNK_SIZE};
use crate::pvec::node::{Node, NODE_SIZE, NODE_BITS, NODE_MASK};
use crate::pvec::memory::{MemoryManager, ManagedRef};
use crate::pvec::cache::IndexCache;

/// A Relaxed Radix Balanced tree implementation.
///
/// This is the internal tree structure that implements the persistent vector's
/// efficient operations. It handles all the complexity of structural sharing,
/// tree balancing, and path copying.
#[derive(Clone)]
pub struct RRBTree<T: Clone> {
    /// The root node of the tree
    root: Option<ManagedRef<Node<T>>>,
    
    /// The height of the tree (number of levels)
    height: usize,
    
    /// The number of elements in the tree
    size: usize,
    
    /// A small buffer for the elements at the end of the vector
    /// This improves performance for consecutive pushes
    tail: ManagedRef<Chunk<T>>,
    
    /// Memory manager for node allocation
    manager: MemoryManager<T>,
    
    /// Index lookup cache for optimizing repeated access patterns
    cache: IndexCache,
}

impl<T: Clone> RRBTree<T> {
    /// Create a new empty RRB tree.
    pub fn new(manager: MemoryManager<T>) -> Self {
        Self {
            root: None,
            height: 0,
            size: 0,
            tail: manager.acquire_chunk(),
            manager,
            cache: IndexCache::new(),
        }
    }
    
    /// Get the number of elements in the tree.
    pub fn len(&self) -> usize {
        self.size
    }
    
    /// Check if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
    
    /// Get the memory manager used by this tree.
    pub fn manager(&self) -> &MemoryManager<T> {
        &self.manager
    }
    
    /// Calculate the effective tree size (excluding the tail).
    fn tree_size(&self) -> usize {
        if self.root.is_none() {
            0
        } else {
            // The tree size is the total size minus the tail size
            let tail_size = self.tail.len();
            if tail_size > self.size {
                0
            } else {
                self.size - tail_size
            }
        }
    }
    
    /// Get the maximum capacity of the tree at its current height.
    fn capacity_at_height(&self, height: usize) -> usize {
        NODE_SIZE.pow(height as u32) * CHUNK_SIZE
    }
    
    /// Check if the tree has reached its capacity at the current height.
    fn is_at_capacity(&self) -> bool {
        if self.root.is_none() {
            return false;
        }
        
        let tree_size = self.tree_size();
        let capacity = self.capacity_at_height(self.height);
        tree_size >= capacity
    }
    
    /// Get an element at the specified index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.size {
            return None;
        }
        
        // Check the tail first
        let tail_offset = self.size - self.tail.len();
        if index >= tail_offset {
            return self.tail.get(index - tail_offset);
        }
        
        // Use cache if available
        if self.cache.has_path_to(index, self.height) {
            return self.get_from_cache(index);
        }
        
        // Fall back to tree traversal
        self.get_from_tree(index)
    }
    
    /// Try to get an element using the cached path.
    fn get_from_cache(&self, index: usize) -> Option<&T> {
        if self.root.is_none() {
            return None;
        }
        
        // Start from the root
        let mut node = self.root.as_ref().unwrap();
        let mut level = self.height;
        let mut remaining_index = index;
        
        // Follow the cached path as far as possible
        while level > 0 {
            // If we have cached information for this level, use it
            if let Some(cached_path_index) = self.cache.get_path_index(self.height - level) {
                match node.as_ref() {
                    Node::Branch { children, sizes } => {
                        let child_index = if cached_path_index < children.len() &&
                                           children[cached_path_index].is_some() {
                            cached_path_index
                        } else {
                            // Calculate child index if cached one is invalid
                            if let Some(sizes) = sizes {
                                // For relaxed nodes, binary search the size table
                                let mut idx = 0;
                                let mut left = 0;
                                let mut right = sizes.len();
                                
                                while left < right {
                                    let mid = left + (right - left) / 2;
                                    if mid < sizes.len() && sizes[mid] <= remaining_index {
                                        left = mid + 1;
                                        idx = mid;
                                    } else {
                                        right = mid;
                                    }
                                }
                                
                                idx
                            } else {
                                // For regular nodes, use bit operations
                                let shift = level * NODE_BITS;
                                (remaining_index >> shift) & NODE_MASK
                            }
                        };
                        
                        // Calculate the new remaining index
                        let sub_index = if let Some(sizes) = sizes {
                            let prev_size = if child_index > 0 { sizes[child_index - 1] } else { 0 };
                            remaining_index - prev_size
                        } else {
                            let shift = level * NODE_BITS;
                            remaining_index & ((1 << shift) - 1)
                        };
                        
                        if let Some(Some(child)) = children.get(child_index) {
                            node = child;
                            remaining_index = sub_index;
                            level -= 1;
                        } else {
                            // Invalid path, fall back to normal traversal
                            return self.get_from_tree(index);
                        }
                    },
                    _ => return self.get_from_tree(index), // Not a branch node, fall back
                }
            } else {
                // No cached information for this level, fall back
                return self.get_from_tree(index);
            }
        }
        
        // At leaf level
        match node.as_ref() {
            Node::Leaf { elements } => elements.get(remaining_index),
            _ => None, // Should not happen in a valid tree
        }
    }
    
    /// Get an element by traversing the tree.
    fn get_from_tree(&self, index: usize) -> Option<&T> {
        if self.root.is_none() {
            return None;
        }
        
        let mut node = self.root.as_ref().unwrap();
        let mut level = self.height;
        let mut remaining_index = index;
        
        // Update the cache with the path we take
        let mut cache_path = Vec::with_capacity(self.height + 1);
        let mut cache_ranges = Vec::with_capacity(self.height + 1);
        
        // Add the root level to the cache
        cache_path.push(0);
        cache_ranges.push(0..self.tree_size());
        
        // Traverse down the tree
        while level > 0 {
            match node.as_ref() {
                Node::Branch { children, sizes } => {
                    // Determine which child contains our index
                    let child_index = if let Some(sizes) = sizes {
                        // For relaxed nodes, binary search the size table
                        let mut idx = 0;
                        let mut found = false;
                        
                        for (i, &size) in sizes.iter().enumerate() {
                            if remaining_index < size {
                                idx = i;
                                found = true;
                                break;
                            }
                        }
                        
                        if !found && !sizes.is_empty() {
                            idx = sizes.len() - 1;
                        }
                        
                        idx
                    } else {
                        // For regular nodes, use bit operations
                        let shift = level * NODE_BITS;
                        (remaining_index >> shift) & NODE_MASK
                    };
                    
                    // Update remaining index
                    if let Some(sizes) = sizes {
                        let prev_size = if child_index > 0 { sizes[child_index - 1] } else { 0 };
                        remaining_index -= prev_size;
                    } else {
                        let shift = level * NODE_BITS;
                        remaining_index &= (1 << shift) - 1;
                    }
                    
                    // Get child node
                    if child_index < children.len() {
                        if let Some(child) = &children[child_index] {
                            node = child;
                            
                            // Update cache
                            cache_path.push(child_index);
                            let start = if child_index > 0 && sizes.is_some() {
                                sizes.as_ref().unwrap()[child_index - 1]
                            } else {
                                0
                            };
                            
                            let end = if sizes.is_some() {
                                sizes.as_ref().unwrap()[child_index]
                            } else {
                                (child_index + 1) * NODE_SIZE.pow(level as u32)
                            };
                            
                            cache_ranges.push(start..end);
                            
                            level -= 1;
                        } else {
                            return None;
                        }
                    } else {
                        return None;
                    }
                },
                _ => return None, // Should never happen at non-leaf levels
            }
        }
        
        // At leaf level, return the element
        match node.as_ref() {
            Node::Leaf { elements } => elements.get(remaining_index),
            _ => None, // Should never happen
        }
    }
    
    /// Update an element at the specified index.
    pub fn update(&self, index: usize, value: T) -> Option<Self> {
        if index >= self.size {
            return None;
        }
        
        // Check if we're updating in the tail
        let tail_offset = self.size - self.tail.len();
        if index >= tail_offset {
            let tail_index = index - tail_offset;
            let mut new_tail = self.tail.clone();
            let result;
            
            match new_tail.make_mut() {
                Ok(chunk) => {
                    if let Some(elem) = chunk.get_mut(tail_index) {
                        *elem = value.clone();
                        result = Some(self.clone());
                    } else {
                        result = None;
                    }
                },
                Err(mut new_chunk) => {
                    if let Some(elem) = new_chunk.get_mut().unwrap().get_mut(tail_index) {
                        *elem = value.clone();
                        new_tail = new_chunk;
                        result = Some(Self {
                            root: self.root.clone(),
                            height: self.height,
                            size: self.size,
                            tail: new_tail,
                            manager: self.manager.clone(),
                            cache: IndexCache::new(), // Invalidate cache on mutation
                        });
                    } else {
                        result = None;
                    }
                }
            }
            
            return result;
        }
        
        // Update in the tree structure
        if self.root.is_none() {
            return None;
        }
        
        let root = self.root.as_ref().unwrap();
        let new_root = root.update(&self.manager, index, value.clone(), self.height * NODE_BITS)?;
        
        Some(Self {
            root: Some(new_root),
            height: self.height,
            size: self.size,
            tail: self.tail.clone(),
            manager: self.manager.clone(),
            cache: IndexCache::new(), // Invalidate cache on mutation
        })
    }
    
    /// Add an element to the end of the tree.
    pub fn push_back(&self, value: T) -> Self {
        // Try to add to the tail first
        if self.tail.len() < CHUNK_SIZE {
            let mut new_tail = self.tail.clone();
            match new_tail.make_mut() {
                Ok(chunk) => {
                    chunk.push_back(value.clone());
                },
                Err(mut new_chunk) => {
                    new_chunk.get_mut().unwrap().push_back(value.clone());
                    new_tail = new_chunk;
                }
            }
            
            return Self {
                root: self.root.clone(),
                height: self.height,
                size: self.size + 1,
                tail: new_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(), // Invalidate cache on mutation
            };
        }
        
        // Tail is full, need to incorporate it into the tree
        let old_tail_clone = self.tail.clone();
        let mut new_tail = self.manager.acquire_chunk();
        new_tail.get_mut().unwrap().push_back(value.clone());
        
        if self.root.is_none() {
            // First element in the tree
            let mut leaf_node = self.manager.acquire_node();
            *leaf_node.get_mut().unwrap() = Node::Leaf { elements: old_tail_clone };
            
            return Self {
                root: Some(leaf_node),
                height: 1,
                size: self.size + 1,
                tail: new_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
        }
        
        // Check if we need to increase the tree height
        if self.is_at_capacity() {
            return self.grow_tree_for_push_back(old_tail_clone, new_tail);
        }
        
        // Add the tail to the existing tree
        let root = self.root.as_ref().unwrap();
        
        // Create a leaf node for the old tail
        let mut leaf_node = self.manager.acquire_node();
        *leaf_node.get_mut().unwrap() = Node::Leaf { elements: old_tail_clone };
        
        let (new_root, _, _) = root.push_back(&self.manager, value.clone(), self.height * NODE_BITS);
        
        Self {
            root: Some(new_root),
            height: self.height,
            size: self.size + 1,
            tail: new_tail,
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        }
    }
    
    /// Grow the tree to accommodate a push_back operation.
    fn grow_tree_for_push_back(&self, old_tail: ManagedRef<Chunk<T>>, new_tail: ManagedRef<Chunk<T>>) -> Self {
        // Create a leaf node from the old tail
        let mut leaf_node = self.manager.acquire_node();
        *leaf_node.get_mut().unwrap() = Node::Leaf { elements: old_tail.clone() };
        
        // If the tree is empty, create a new tree with one branch and one leaf
        if self.root.is_none() {
            // Current vector only has elements in the tail
            // Move tail to root and make a new tail with value
            let mut tail_node = self.manager.acquire_node();
            *tail_node.get_mut().unwrap() = Node::Leaf { elements: self.tail.clone() };
            
            // Create a new branch node
            let mut new_root = self.manager.acquire_node();
            match new_root.get_mut().unwrap() {
                Node::Branch { children, sizes } => {
                    children.push(Some(leaf_node));
                    children.push(Some(tail_node));
                    
                    *sizes = Some(vec![1, self.size + 1]);
                },
                _ => unreachable!()
            }
            
            return Self {
                root: Some(new_root),
                height: 1,
                size: self.size,
                tail: new_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
        }
        
        // If there's room in the current tree, add the tail as a leaf
        if !self.is_at_capacity() {
            // Create a new tree with the old tail added as a leaf
            let mut new_tree = self.clone();
            new_tree.size = self.size;
            new_tree.tail = new_tail;
            
            // Add the old tail as a leaf to the tree
            // TODO: Implement this
            
            return new_tree;
        }
        
        // Otherwise, grow the tree's height by creating a new root
        let mut new_root = self.manager.acquire_node();
        match new_root.get_mut().unwrap() {
            Node::Branch { children, sizes } => {
                // Add the current root as the first child
                if let Some(old_root) = &self.root {
                    children.push(Some(old_root.clone()));
                }
                
                // Add the old tail as the second child
                children.push(Some(leaf_node));
                
                // Create size table
                let old_tree_size = self.tree_size();
                let old_tail_clone = old_tail.clone();
                let old_tail_len = old_tail_clone.len();
                let total_size = old_tree_size + old_tail_len;
                *sizes = Some(vec![old_tree_size, total_size]);
            },
            _ => unreachable!() // Should be a branch node
        }
        
        Self {
            root: Some(new_root),
            height: self.height + 1,
            size: self.size + 1,
            tail: new_tail,
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        }
    }
    
    /// Add an element to the beginning of the tree.
    pub fn push_front(&self, value: T) -> Self {
        if self.is_empty() {
            // First element, just add to tail
            let mut new_tail = self.manager.acquire_chunk();
            new_tail.get_mut().unwrap().push_back(value.clone());
            
            return Self {
                root: None,
                height: 0,
                size: 1,
                tail: new_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
        }
        
        // Create a new chunk with just the new value
        let mut chunk = self.manager.acquire_chunk();
        chunk.get_mut().unwrap().push_back(value.clone());
        
        // Create a leaf node for the new value
        let mut leaf_node = self.manager.acquire_node();
        *leaf_node.get_mut().unwrap() = Node::Leaf { elements: chunk };
        
        if self.root.is_none() {
            // Current vector only has elements in the tail
            // Move tail to root and make a new tail with value
            let mut tail_node = self.manager.acquire_node();
            *tail_node.get_mut().unwrap() = Node::Leaf { elements: self.tail.clone() };
            
            // Create a new branch node
            let mut new_root = self.manager.acquire_node();
            match new_root.get_mut().unwrap() {
                Node::Branch { children, sizes } => {
                    children.push(Some(leaf_node));
                    children.push(Some(tail_node));
                    
                    *sizes = Some(vec![1, self.size + 1]);
                },
                _ => unreachable!()
            }
            
            return Self {
                root: Some(new_root),
                height: 1,
                size: self.size + 1,
                tail: self.tail.clone(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
        }
        
        // Try to add to existing tree
        if self.is_at_capacity() {
            // Tree is full, need to increase height
            let mut new_root = self.manager.acquire_node();
            match new_root.get_mut().unwrap() {
                Node::Branch { children, sizes } => {
                    children.push(Some(leaf_node));
                    children.push(Some(self.root.as_ref().unwrap().clone()));
                    
                    let old_tree_size = self.tree_size();
                    let total_size = old_tree_size + 1;
                    *sizes = Some(vec![1, total_size]);
                },
                _ => unreachable!()
            }
            
            return Self {
                root: Some(new_root),
                height: self.height + 1,
                size: self.size + 1,
                tail: self.tail.clone(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
        }
        
        // Add to existing tree
        let root = self.root.as_ref().unwrap();
        let (new_root, _, _) = root.push_front(&self.manager, value.clone(), self.height * NODE_BITS);
        
        Self {
            root: Some(new_root),
            height: self.height,
            size: self.size + 1,
            tail: self.tail.clone(),
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        }
    }
    
    /// Remove the last element from the tree.
    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }
        
        // Try to pop from the tail first
        if !self.tail.is_empty() {
            let mut new_tail = self.tail.clone();
            let result;
            
            match new_tail.make_mut() {
                Ok(chunk) => {
                    result = chunk.pop_back();
                },
                Err(mut new_chunk) => {
                    result = new_chunk.get_mut().unwrap().pop_back();
                    new_tail = new_chunk;
                }
            }
            
            if let Some(value) = result {
                let new_tree = Self {
                    root: self.root.clone(),
                    height: self.height,
                    size: self.size - 1,
                    tail: new_tail,
                    manager: self.manager.clone(),
                    cache: IndexCache::new(),
                };
                
                return Some((new_tree, value));
            }
            
            return None; // This shouldn't happen if tail was non-empty
        }
        
        // Tail is empty, need to get a new tail from the tree
        if self.root.is_none() {
            return None;
        }
        
        let root = self.root.as_ref().unwrap();
        let (new_root, popped_value) = root.pop_back(&self.manager, self.height * NODE_BITS);
        
        if let Some(value) = popped_value {
            // Check if we need to fill a new tail
            if new_root.is_empty() {
                // Tree is now empty
                return Some((Self::new(self.manager.clone()), value));
            }
            
            // Extract the rightmost leaf to become the new tail
            let mut new_tree = self.clone();
            new_tree.root = Some(new_root);
            new_tree.size = self.size - 1;
            
            // Extract a new tail from the tree
            if new_tree.size > 0 {
                let (final_tree, new_tail) = new_tree.extract_tail();
                new_tree = final_tree;
                new_tree.tail = new_tail;
            }
            
            return Some((new_tree, value));
        }
        
        None
    }
    
    /// Remove the first element from the tree.
    pub fn pop_front(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }
        
        // If there's only one element, it's in the tail
        if self.size == 1 {
            let value = self.tail.get(0)?.clone();
            return Some((Self::new(self.manager.clone()), value));
        }
        
        // If the root is None, all elements are in the tail
        if self.root.is_none() {
            let mut new_tail = self.tail.clone();
            let result;
            
            match new_tail.make_mut() {
                Ok(chunk) => {
                    result = chunk.pop_front();
                },
                Err(mut new_chunk) => {
                    result = new_chunk.get_mut().unwrap().pop_front();
                    new_tail = new_chunk;
                }
            }
            
            if let Some(value) = result {
                let new_tree = Self {
                    root: None,
                    height: 0,
                    size: self.size - 1,
                    tail: new_tail,
                    manager: self.manager.clone(),
                    cache: IndexCache::new(),
                };
                
                return Some((new_tree, value));
            }
            
            return None;
        }
        
        // Pop from the tree
        let root = self.root.as_ref().unwrap();
        let (new_root, popped_value) = root.pop_front(&self.manager, self.height * NODE_BITS);
        
        if let Some(value) = popped_value {
            let mut new_tree = Self {
                root: Some(new_root),
                height: self.height,
                size: self.size - 1,
                tail: self.tail.clone(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Check if the tree is now empty
            if new_tree.tree_size() == 0 {
                new_tree.root = None;
                new_tree.height = 0;
            } else if new_tree.height > 0 && new_tree.root.as_ref().unwrap().child_count() == 1 {
                // Tree has collapsed, reduce height
                new_tree = new_tree.shrink_tree();
            }
            
            return Some((new_tree, value));
        }
        
        None
    }
    
    /// Helper method to extract the rightmost leaf as a new tail.
    fn extract_tail(&self) -> (Self, ManagedRef<Chunk<T>>) {
        // Extract the rightmost leaf node from the tree to become a new tail
        // This is used when we need to get the preceding elements before the current tail,
        // after operations like pop_back
        
        if self.root.is_none() {
            return (self.clone(), self.manager.acquire_chunk());
        }
        
        let root = self.root.as_ref().unwrap();
        
        // If the tree has height 1, the rightmost leaf becomes the tail
        if self.height == 1 {
            match root.as_ref() {
                Node::Branch { children, .. } => {
                    if !children.is_empty() {
                        if let Some(Some(last_child)) = children.last() {
                            match last_child.as_ref() {
                                Node::Leaf { elements } => {
                                    // Create a new tree without the last leaf
                                    let mut new_root = self.manager.acquire_node();
                                    match new_root.get_mut().unwrap() {
                                        Node::Branch { children: new_children, sizes: new_sizes } => {
                                            // Copy all but the last child
                                            for i in 0..children.len() - 1 {
                                                new_children.push(children[i].clone());
                                            }
                                            
                                            // Update sizes if needed
                                            if let Node::Branch { sizes, .. } = root.as_ref() {
                                                if let Some(sizes) = sizes {
                                                    let mut new_size_table = Vec::with_capacity(sizes.len() - 1);
                                                    
                                                    for i in 0..sizes.len() - 1 {
                                                        new_size_table.push(sizes[i]);
                                                    }
                                                    
                                                    *new_sizes = Some(new_size_table);
                                                }
                                            }
                                        },
                                        _ => unreachable!()
                                    }
                                    
                                    let new_tree = Self {
                                        root: if new_root.child_count() > 0 { Some(new_root.clone()) } else { None },
                                        height: if new_root.child_count() > 0 { self.height } else { 0 },
                                        size: self.size - elements.len(),
                                        tail: self.tail.clone(),
                                        manager: self.manager.clone(),
                                        cache: IndexCache::new(),
                                    };
                                    
                                    return (new_tree, elements.clone());
                                },
                                _ => {}
                            }
                        }
                    }
                },
                _ => {}
            }
        }
        
        // For taller trees, traverse to the rightmost leaf
        let (new_root, extracted_tail) = self.extract_rightmost_leaf(self.root.as_ref().unwrap(), self.height - 1);
        
        if let Some(tail) = extracted_tail {
            let mut new_tree = Self {
                root: Some(new_root),
                height: self.height,
                size: self.size - tail.len(),
                tail: self.tail.clone(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Check if the tree has collapsed and needs to shrink
            if new_tree.height > 0 && new_tree.root.as_ref().unwrap().child_count() <= 1 {
                new_tree = new_tree.shrink_tree();
            }
            
            return (new_tree, tail);
        }
        
        // This shouldn't happen with a valid tree
        (self.clone(), self.manager.acquire_chunk())
    }
    
    fn extract_rightmost_leaf(
        &self,
        node: &ManagedRef<Node<T>>,
        level: usize
    ) -> (ManagedRef<Node<T>>, Option<ManagedRef<Chunk<T>>>) {
        match node.as_ref() {
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    return (node.clone(), None);
                }
                
                let last_idx = children.len() - 1;
                if let Some(last_child) = &children[last_idx] {
                    let (new_child, extracted_leaf) = self.extract_rightmost_leaf(last_child, level - 1);
                    
                    if extracted_leaf.is_none() {
                        return (node.clone(), None);
                    }
                    
                    // Create a new node without the extracted leaf
                    let mut new_node = self.manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children: new_children, sizes: new_sizes } => {
                            // Copy all children except the last one if it's empty
                            for i in 0..last_idx {
                                new_children.push(children[i].clone());
                            }
                            
                            // Add the new last child if it's not empty
                            if !new_child.is_empty() {
                                new_children.push(Some(new_child));
                            }
                            
                            // Update size table
                            if let Some(_old_sizes) = sizes {
                                let mut new_size_table = Vec::with_capacity(new_children.len());
                                
                                for i in 0..new_children.len() {
                                    if let Some(Some(child)) = new_children.get(i) {
                                        let child_size = if i > 0 {
                                            child.size() + new_size_table[i - 1]
                                        } else {
                                            child.size()
                                        };
                                        
                                        new_size_table.push(child_size);
                                    }
                                }
                                
                                *new_sizes = if !new_size_table.is_empty() { Some(new_size_table) } else { None };
                            }
                        },
                        _ => unreachable!()
                    }
                    
                    return (new_node, extracted_leaf);
                }
                
                (node.clone(), None)
            },
            Node::Leaf { elements } => {
                if level > 0 {
                    // This shouldn't happen in a valid tree
                    return (node.clone(), None);
                }
                
                // Create an empty leaf node to replace this one
                let mut empty_leaf = self.manager.acquire_node();
                *empty_leaf.get_mut().unwrap() = Node::Leaf { elements: self.manager.acquire_chunk() };
                
                (empty_leaf, Some(elements.clone()))
            }
        }
    }
        
    /// Reduce the height of the tree if possible.
    fn shrink_tree(&self) -> Self {
        if self.root.is_none() || self.height <= 1 {
            return self.clone();
        }
        
        let root = self.root.as_ref().unwrap();
        
        match root.as_ref() {
            Node::Branch { children, .. } => {
                if children.len() != 1 {
                    return self.clone();
                }
                
                if let Some(Some(only_child)) = children.get(0) {
                    // Shrink by one level
                    return Self {
                        root: Some(only_child.clone()),
                        height: self.height - 1,
                        size: self.size,
                        tail: self.tail.clone(),
                        manager: self.manager.clone(),
                        cache: IndexCache::new(),
                    };
                }
            },
            _ => {}
        }
        
        self.clone()
    }
        
    /// Concatenate two trees.
    pub fn concat(&self, other: &Self) -> Self {
        // Handle empty trees
        if self.is_empty() {
            return other.clone();
        }
        
        if other.is_empty() {
            return self.clone();
        }
        
        // Handle special case where one or both trees have only a tail
        if self.root.is_none() && other.root.is_none() {
            // Both trees only have tails
            let mut combined_chunk = self.manager.acquire_chunk();
            let manager = &self.manager;
            
            // Try to combine the tails
            let total_len = self.tail.len() + other.tail.len();
            
            // Copy elements from self.tail
            for i in 0..self.tail.len() {
                if let Some(value) = self.tail.get(i) {
                    match combined_chunk.make_mut() {
                        Ok(chunk) => { chunk.push_back(value.clone()); }
                        Err(mut new_chunk) => {
                            new_chunk.get_mut().unwrap().push_back(value.clone());
                            combined_chunk = new_chunk;
                        }
                    }
                }
            }
            
            // Copy elements from other.tail
            for i in 0..other.tail.len() {
                if let Some(value) = other.tail.get(i) {
                    match combined_chunk.make_mut() {
                        Ok(chunk) => { chunk.push_back(value.clone()); }
                        Err(mut new_chunk) => {
                            new_chunk.get_mut().unwrap().push_back(value.clone());
                            combined_chunk = new_chunk;
                        }
                    }
                }
            }
            
            if total_len <= CHUNK_SIZE {
                // Can fit in a single chunk
                return Self {
                    root: None,
                    height: 0,
                    size: total_len,
                    tail: combined_chunk,
                    manager: manager.clone(),
                    cache: IndexCache::new(),
                };
            }
            
            // Need to create a tree with the combined elements
            let mut tree = Self {
                root: None,
                height: 0,
                size: 0,
                tail: manager.acquire_chunk(),
                manager: manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Add all elements to the tree
            for i in 0..combined_chunk.len() {
                if let Some(value) = combined_chunk.get(i) {
                    tree = tree.push_back(value.clone());
                }
            }
            
            return tree;
        }
        
        // If either tree has only a tail, convert it to a regular tree
        let left_tree = if self.root.is_none() {
            let mut tree = Self {
                root: None,
                height: 0,
                size: 0,
                tail: self.manager.acquire_chunk(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Add all elements from tail
            for i in 0..self.tail.len() {
                if let Some(value) = self.tail.get(i) {
                    tree = tree.push_back(value.clone());
                }
            }
            
            tree
        } else {
            self.clone()
        };
        
        let right_tree = if other.root.is_none() {
            let mut tree = Self {
                root: None,
                height: 0,
                size: 0,
                tail: self.manager.acquire_chunk(),
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Add all elements from tail
            for i in 0..other.tail.len() {
                if let Some(value) = other.tail.get(i) {
                    tree = tree.push_back(value.clone());
                }
            }
            
            tree
        } else {
            other.clone()
        };
        
        // Get the heights of both trees
        let self_height = left_tree.height;
        let other_height = right_tree.height;
        
        // Normalize heights
        let (left, right, new_height) = match self_height.cmp(&other_height) {
            std::cmp::Ordering::Equal => {
                (left_tree.root.clone(), right_tree.root.clone(), self_height)
            },
            std::cmp::Ordering::Greater => {
                // Left tree is taller, elevate right tree
                let elevated_right = self.elevate_tree(right_tree.root.clone(), self_height - other_height);
                (left_tree.root.clone(), elevated_right, self_height)
            },
            std::cmp::Ordering::Less => {
                // Right tree is taller, elevate left tree
                let elevated_left = self.elevate_tree(left_tree.root.clone(), other_height - self_height);
                (elevated_left, right_tree.root.clone(), other_height)
            }
        };
        
        // Join the trees
        let mut joined = false;
        let mut new_root = self.manager.acquire_node();
        
        if let (Some(left_root), Some(right_root)) = (&left, &right) {
            match (left_root.as_ref(), right_root.as_ref()) {
                (Node::Branch { children: left_children, sizes: left_sizes },
                 Node::Branch { children: right_children, sizes: right_sizes }) => {
                    
                    // Check if we can join them directly
                    let left_count = left_children.len();
                    let right_count = right_children.len();
                    
                    if left_count + right_count <= NODE_SIZE {
                        // Can combine directly
                        match new_root.get_mut().unwrap() {
                            Node::Branch { children, sizes } => {
                                // Copy left children
                                for child in left_children.iter() {
                                    children.push(child.clone());
                                }
                                
                                // Copy right children
                                for child in right_children.iter() {
                                    children.push(child.clone());
                                }
                                
                                // Create size table
                                let mut size_table = Vec::with_capacity(left_count + right_count);
                                let left_size = left_tree.tree_size();
                                
                                if let (Some(left_sizes), Some(right_sizes)) = (left_sizes, right_sizes) {
                                    // Both relaxed
                                    for &size in left_sizes.iter() {
                                        size_table.push(size);
                                    }
                                    
                                    for &size in right_sizes.iter() {
                                        size_table.push(left_size + size);
                                    }
                                } else if let Some(left_sizes) = left_sizes {
                                    // Left relaxed
                                    for &size in left_sizes.iter() {
                                        size_table.push(size);
                                    }
                                    
                                    let mut sum = left_size;
                                    for child in right_children.iter().filter_map(|c| c.as_ref()) {
                                        sum += child.size();
                                        size_table.push(sum);
                                    }
                                } else if let Some(right_sizes) = right_sizes {
                                    // Right relaxed
                                    let mut sum = 0;
                                    for child in left_children.iter().filter_map(|c| c.as_ref()) {
                                        sum += child.size();
                                        size_table.push(sum);
                                    }
                                    
                                    for &size in right_sizes.iter() {
                                        size_table.push(left_size + size);
                                    }
                                } else {
                                    // Neither relaxed
                                    let mut sum = 0;
                                    
                                    for child in left_children.iter().filter_map(|c| c.as_ref()) {
                                        sum += child.size();
                                        size_table.push(sum);
                                    }
                                    
                                    for child in right_children.iter().filter_map(|c| c.as_ref()) {
                                        sum += child.size();
                                        size_table.push(sum);
                                    }
                                }
                                
                                *sizes = Some(size_table);
                                joined = true;
                            },
                            _ => unreachable!()
                        }
                    }
                },
                _ => {}
            }
        }
        
        if !joined {
            // Need to create a parent node
            match new_root.get_mut().unwrap() {
                Node::Branch { children, sizes } => {
                    if let Some(left_node) = &left {
                        children.push(Some(left_node.clone()));
                    }
                    
                    if let Some(right_node) = &right {
                        children.push(Some(right_node.clone()));
                    }
                    
                    // Create size table
                    let left_size = left_tree.tree_size();
                    let total_size = left_size + right_tree.tree_size();
                    *sizes = Some(vec![left_size, total_size]);
                },
                _ => unreachable!()
            }
        }
        
        // Create final tree
        let total_size = left_tree.size + right_tree.size;
        let right_tail = right_tree.tail.clone();
        
        Self {
            root: Some(new_root),
            height: new_height + 1,
            size: total_size,
            tail: right_tail,
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        }
    }
    
    /// Elevate a tree to a greater height.
    fn elevate_tree(&self, node: Option<ManagedRef<Node<T>>>, levels: usize) -> Option<ManagedRef<Node<T>>> {
        if levels == 0 || node.is_none() {
            return node;
        }
        
        let mut current = node;
        
        for _ in 0..levels {
            let mut branch = self.manager.acquire_node();
            
            match branch.get_mut().unwrap() {
                Node::Branch { children, sizes } => {
                    if let Some(current_node) = current {
                        let current_node_clone = current_node.clone();
                        children.push(Some(current_node_clone));
                        *sizes = Some(vec![current_node.size()]);
                    }
                },
                _ => unreachable!()
            }
            
            current = Some(branch);
        }
        
        current
    }
    
    /// Split the tree at the given index.
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index == 0 {
            return (Self::new(self.manager.clone()), self.clone());
        }
        
        if index >= self.size {
            return (self.clone(), Self::new(self.manager.clone()));
        }
        
        // Handle special case where split point is in the tail
        let tail_offset = self.size - self.tail.len();
        if index >= tail_offset {
            // Split point is in the tail
            let tail_index = index - tail_offset;
            
            // Create a split tail
            let mut left_tail = self.manager.acquire_chunk();
            let mut right_tail = self.manager.acquire_chunk();
            
            // Copy elements to the left and right tails
            for i in 0..tail_index {
                if let Some(value) = self.tail.get(i) {
                    left_tail.get_mut().unwrap().push_back(value.clone());
                }
            }
            
            for i in tail_index..self.tail.len() {
                if let Some(value) = self.tail.get(i) {
                    right_tail.get_mut().unwrap().push_back(value.clone());
                }
            }
            
            // Left part has the tree with a new tail
            let left = Self {
                root: self.root.clone(),
                height: self.height,
                size: tail_offset + left_tail.len(),
                tail: left_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            // Right part has just the tail
            let right = Self {
                root: None,
                height: 0,
                size: right_tail.len(),
                tail: right_tail,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            };
            
            return (left, right);
        }
        
        // Split point is in the tree
        if self.root.is_none() {
            return (self.clone(), Self::new(self.manager.clone()));
        }
        
        let root = self.root.as_ref().unwrap();
        let (left_root, right_root) = root.split(&self.manager, index, self.height * NODE_BITS);
        
        // Create left tree
        let mut left = Self {
            root: Some(left_root),
            height: self.height,
            size: index,
            tail: self.manager.acquire_chunk(),
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        };
        
        // Extract the rightmost elements of the left tree to form its tail
        if !left.is_empty() {
            let (new_left, left_tail) = left.extract_tail();
            left = new_left;
            left.tail = left_tail;
        }
        
        // Create right tree with the original tail
        let mut right = Self {
            root: Some(right_root),
            height: self.height,
            size: self.size - index,
            tail: self.tail.clone(),
            manager: self.manager.clone(),
            cache: IndexCache::new(),
        };
        
        // Shrink trees if necessary
        if left.height > 0 && left.root.as_ref().unwrap().child_count() <= 1 {
            left = left.shrink_tree();
        }
        
        if right.height > 0 && right.root.as_ref().unwrap().child_count() <= 1 {
            right = right.shrink_tree();
        }
        
        (left, right)
    }
}

impl<T: Clone + PartialEq> PartialEq for RRBTree<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.size != other.size {
            return false;
        }
        
        for i in 0..self.size {
            if self.get(i) != other.get(i) {
                return false;
            }
        }
        
        true
    }
}

impl<T: Clone + Eq> Eq for RRBTree<T> {}