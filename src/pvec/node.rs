//! Tree Node Module
//!
//! This module defines the Node type, which is the building block
//! for the internal tree structure of the persistent vector.

use std::fmt::{self, Debug};

use crate::pvec::chunk::{Chunk, CHUNK_SIZE, CHUNK_BITS};
use crate::pvec::memory::{ManagedRef, MemoryManager};

/// The maximum number of children a node can have.
pub const NODE_SIZE: usize = CHUNK_SIZE;

/// Bit mask for extracting the index within a node.
pub const NODE_MASK: usize = NODE_SIZE - 1;

/// The number of bits needed to represent indices within a node.
pub const NODE_BITS: usize = CHUNK_BITS;

/// A node in the RRB tree.
///
/// Nodes can be either internal nodes (containing other nodes)
/// or leaf nodes (containing values directly in a chunk).
#[derive(Clone)]
pub enum Node<T: Clone> {
    /// An internal node containing references to child nodes
    Branch {
        /// Child nodes
        children: Vec<Option<ManagedRef<Node<T>>>>,
        
        /// Optional size table for relaxed nodes
        /// When None, the node is a regular (non-relaxed) node
        sizes: Option<Vec<usize>>,
    },
    
    /// A leaf node containing elements directly
    Leaf {
        /// The elements in this leaf node
        elements: ManagedRef<Chunk<T>>,
    },
}

impl<T: Clone> Node<T> {
    /// Create a new empty branch node.
    pub fn new() -> Self {
        Node::Branch {
            children: Vec::with_capacity(NODE_SIZE),
            sizes: None,
        }
    }
    
    /// Create a new leaf node from a chunk of elements.
    pub fn leaf(chunk: ManagedRef<Chunk<T>>) -> Self {
        Node::Leaf { elements: chunk }
    }

    /// Get the total number of elements contained in this node and its descendants.
    pub fn size(&self) -> usize {
        match self {
            Node::Leaf { elements } => elements.len(),
            Node::Branch { children, sizes } => {
                if let Some(sizes) = sizes {
                    if !sizes.is_empty() {
                        return *sizes.last().unwrap();
                    }
                    return 0;
                }
                
                // For regular nodes, calculate the size based on children
                children.iter()
                    .filter_map(|child| child.as_ref())
                    .map(|child| child.size())
                    .sum()
            }
        }
    }
    
    /// Check if this node is empty (contains no elements).
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }
    
    /// Check if this node is a leaf node.
    pub fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf { .. })
    }
    
    /// Check if this node is a branch node.
    pub fn is_branch(&self) -> bool {
        matches!(self, Node::Branch { .. })
    }
    
    /// Get the number of direct children this node has.
    pub fn child_count(&self) -> usize {
        match self {
            Node::Leaf { .. } => 0,
            Node::Branch { children, .. } => {
                children.iter().filter(|c| c.is_some()).count()
            }
        }
    }
    
    /// Check if this node is a relaxed node (has a size table).
    pub fn is_relaxed(&self) -> bool {
        match self {
            Node::Branch { sizes, .. } => sizes.is_some(),
            Node::Leaf { .. } => false,
        }
    }
    
    /// Convert this node to a relaxed node if it's not already.
    pub fn ensure_relaxed(&mut self) {
        if let Node::Branch { children, sizes } = self {
            if sizes.is_none() {
                let mut size_table = Vec::with_capacity(children.len());
                let mut sum = 0;
                
                for child in children.iter().filter_map(|c| c.as_ref()) {
                    sum += child.size();
                    size_table.push(sum);
                }
                
                *sizes = Some(size_table);
            }
        }
    }
    
    /// Get an element at the specified index.
    ///
    /// The `shift` parameter indicates the level in the tree (shift amount in bits).
    pub fn get(&self, index: usize, shift: usize) -> Option<&T> {
        match self {
            Node::Leaf { elements } => elements.get(index),
            Node::Branch { children, sizes } => {
                let (child_index, sub_index) = if let Some(sizes) = sizes {
                    // For relaxed nodes, binary search the size table
                    let mut idx = 0;
                    let mut left = 0;
                    let mut right = sizes.len();
                    
                    while left < right {
                        let mid = left + (right - left) / 2;
                        if mid < sizes.len() && sizes[mid] <= index {
                            left = mid + 1;
                            idx = mid;
                        } else {
                            right = mid;
                        }
                    }
                    
                    let prev_size = if idx > 0 { sizes[idx - 1] } else { 0 };
                    (idx, index - prev_size)
                } else {
                    // For regular nodes, use bit operations
                    let child_index = (index >> shift) & NODE_MASK;
                    let sub_index = index & ((1 << shift) - 1);
                    (child_index, sub_index)
                };
                
                if child_index < children.len() {
                    if let Some(child) = &children[child_index] {
                        return child.get(sub_index, shift - NODE_BITS);
                    }
                }
                
                None
            }
        }
    }
    
    /// Update an element at the specified index, returning a new node.
    ///
    /// Returns None if the index is out of bounds.
    pub fn update(&self, 
                  manager: &MemoryManager<T>, 
                  index: usize, 
                  value: T, 
                  shift: usize) -> Option<ManagedRef<Node<T>>> {
        match self {
            Node::Leaf { elements } => {
                if index >= elements.len() {
                    return None;
                }
                
                // Clone the chunk and update it
                let mut new_elements = elements.clone();
                let new_chunk_result = new_elements.make_mut();
                let new_chunk = match new_chunk_result {
                    Ok(chunk) => {
                        // We got a mutable reference
                        if let Some(elem) = chunk.get_mut(index) {
                            *elem = value;
                        }
                        new_elements
                    },
                    Err(new_managed_ref) => {
                        // We got a new reference
                        let mut new_chunk = new_managed_ref;
                        if let Some(elem) = new_chunk.get_mut().unwrap().get_mut(index) {
                            *elem = value;
                        }
                        new_chunk
                    }
                };
                
                // Create a new leaf node
                Some(manager.acquire_node().clone()).map(|mut node_ref| {
                    match node_ref.get_mut().unwrap() {
                        Node::Branch { .. } => *node_ref.get_mut().unwrap() = Node::Leaf { elements: new_chunk },
                        Node::Leaf { elements: leaf_elements } => *leaf_elements = new_chunk,
                    }
                    node_ref
                })
            },
            Node::Branch { children, sizes } => {
                let (child_index, sub_index) = if let Some(sizes) = sizes {
                    // For relaxed nodes, binary search the size table
                    let mut idx = 0;
                    let mut left = 0;
                    let mut right = sizes.len();
                    
                    while left < right {
                        let mid = left + (right - left) / 2;
                        if mid < sizes.len() && sizes[mid] <= index {
                            left = mid + 1;
                            idx = mid;
                        } else {
                            right = mid;
                        }
                    }
                    
                    let prev_size = if idx > 0 { sizes[idx - 1] } else { 0 };
                    (idx, index - prev_size)
                } else {
                    // For regular nodes, use bit operations
                    let child_index = (index >> shift) & NODE_MASK;
                    let sub_index = index & ((1 << shift) - 1);
                    (child_index, sub_index)
                };
                
                if child_index >= children.len() || children[child_index].is_none() {
                    return None;
                }
                
                let child = &children[child_index].as_ref().unwrap();
                let new_child = child.update(manager, sub_index, value, shift - NODE_BITS)?;
                
                // Create a new branch node with the updated child
                let mut new_node = manager.acquire_node();
                match new_node.get_mut().unwrap() {
                    Node::Branch { children: new_children, sizes: new_sizes } => {
                        // Copy the children
                        *new_children = children.clone();
                        // Update the child
                        new_children[child_index] = Some(new_child);
                        // Copy the size table if it exists
                        *new_sizes = sizes.clone();
                    },
                    Node::Leaf { .. } => {
                        // Convert to branch
                        let mut new_children = Vec::with_capacity(NODE_SIZE);
                        new_children.resize_with(children.len(), || None);
                        // Copy the children
                        for (i, child) in children.iter().enumerate() {
                            new_children[i] = child.clone();
                        }
                        // Update the child
                        new_children[child_index] = Some(new_child);
                        
                        *new_node.get_mut().unwrap() = Node::Branch {
                            children: new_children,
                            sizes: sizes.clone(),
                        };
                    }
                }
                
                Some(new_node)
            }
        }
    }
    
    /// Push a new element to the end of this node.
    ///
    /// Returns a tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    pub fn push_back(&self, 
                     manager: &MemoryManager<T>, 
                     value: T, 
                     shift: usize) -> (ManagedRef<Node<T>>, bool, Option<ManagedRef<Node<T>>>) {
        match self {
            Node::Leaf { elements } => {
                if elements.len() < CHUNK_SIZE {
                    // Leaf has space, just add the element
                    let mut new_elements = elements.clone();
                    let modified = match new_elements.make_mut() {
                        Ok(chunk) => {
                            chunk.push_back(value);
                            new_elements
                        },
                        Err(mut new_chunk) => {
                            new_chunk.get_mut().unwrap().push_back(value);
                            new_chunk
                        }
                    };
                    
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = Node::Leaf { elements: modified };
                    (new_node, false, None)
                } else {
                    // Leaf is full, need to create two new leaves
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = Node::Leaf { elements: elements.clone() };
                    
                    let mut overflow = manager.acquire_node();
                    *overflow.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                    
                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    // Empty branch, create a new leaf
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    
                    let mut new_leaf = manager.acquire_node();
                    *new_leaf.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                    
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children: new_children, sizes: new_sizes } => {
                            new_children.push(Some(new_leaf));
                            *new_sizes = Some(vec![1]);
                        },
                        _ => unreachable!()
                    }
                    
                    (new_node, false, None)
                } else {
                    let last_idx = children.len() - 1;
                    
                    if let Some(last_child) = &children[last_idx] {
                        // Try to add to the last child
                        let (new_child, was_split, overflow) = 
                            last_child.push_back(manager, value, shift - NODE_BITS);
                        
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: new_children, sizes: new_sizes } => {
                                // Copy children
                                *new_children = children.clone();
                                // Update last child
                                new_children[last_idx] = Some(new_child.clone());
                                
                                // Handle overflow if split occurred
                                if was_split {
                                    if children.len() < NODE_SIZE {
                                        // We have space for the overflow
                                        let overflow_clone = overflow.clone();
                                        new_children.push(overflow_clone);
                                        
                                        // Update size table
                                        if let Some(old_sizes) = sizes {
                                            let mut new_size_table = old_sizes.clone();
                                            let new_size = new_size_table.last().unwrap_or(&0) + 1;
                                            new_size_table.push(new_size);
                                            *new_sizes = Some(new_size_table);
                                        } else {
                                            // Convert to relaxed node
                                            let mut size_table = Vec::with_capacity(new_children.len());
                                            let mut sum = 0;
                                            
                                            for child in new_children.iter().filter_map(|c| c.clone()) {
                                                sum += child.size();
                                                size_table.push(sum);
                                            }
                                            
                                            *new_sizes = Some(size_table);
                                        }
                                        
                                        (new_node, false, None)
                                    } else {
                                        // Node is full, we need to split
                                        let mut overflow_node = manager.acquire_node();
                                        match overflow_node.get_mut().unwrap() {
                                            Node::Branch { children: overflow_children, sizes: overflow_sizes } => {
                                                let overflow_clone = overflow.clone();
                                                overflow_children.push(overflow_clone);
                                                *overflow_sizes = Some(vec![overflow.unwrap().size()]);
                                            },
                                            _ => unreachable!()
                                        }
                                        
                                        (new_node, true, Some(overflow_node))
                                    }
                                } else {
                                    // No split, just update size table if needed
                                    if let Some(old_sizes) = sizes {
                                        let mut new_size_table = old_sizes.clone();
                                        let new_child_clone = new_child.clone();
                                        let size_inc = new_child_clone.size() - last_child.size();
                                        
                                        for size in new_size_table.iter_mut() {
                                            *size += size_inc;
                                        }
                                        
                                        *new_sizes = Some(new_size_table);
                                    }
                                    
                                    (new_node, false, None)
                                }
                            },
                            _ => unreachable!()
                        }
                    } else {
                        // Empty slot at the end, create a new leaf
                        let mut new_chunk = manager.acquire_chunk();
                        new_chunk.get_mut().unwrap().push_back(value);
                        
                        let mut new_leaf = manager.acquire_node();
                        *new_leaf.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                        
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: new_children, sizes: new_sizes } => {
                                // Copy children
                                *new_children = children.clone();
                                // Set the last child
                                new_children[last_idx] = Some(new_leaf.clone());
                                
                                // Update size table
                                if let Some(old_sizes) = sizes {
                                    let mut new_size_table = old_sizes.clone();
                                    let leaf_size = new_leaf.size();
                                    
                                    if last_idx < new_size_table.len() {
                                        new_size_table[last_idx] = leaf_size;
                                    } else {
                                        new_size_table.push(leaf_size);
                                    }
                                    
                                    *new_sizes = Some(new_size_table);
                                }
                            },
                            _ => unreachable!()
                        }
                        
                        (new_node, false, None)
                    }
                }
            }
        }
    }

    /// Push a new element to the front of this node.
    ///
    /// Returns a tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    pub fn push_front(&self, 
                      manager: &MemoryManager<T>, 
                      value: T, 
                      shift: usize) -> (ManagedRef<Node<T>>, bool, Option<ManagedRef<Node<T>>>) {
        match self {
            Node::Leaf { elements } => {
                if elements.len() < CHUNK_SIZE {
                    // Leaf has space, just add the element
                    let mut new_elements = elements.clone();
                    let modified = match new_elements.make_mut() {
                        Ok(chunk) => {
                            chunk.push_front(value);
                            new_elements
                        },
                        Err(mut new_chunk) => {
                            new_chunk.get_mut().unwrap().push_front(value);
                            new_chunk
                        }
                    };
                    
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = Node::Leaf { elements: modified };
                    (new_node, false, None)
                } else {
                    // Leaf is full, need to create two new leaves
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    
                    let mut overflow = manager.acquire_node();
                    *overflow.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                    
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = Node::Leaf { elements: elements.clone() };
                    
                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    // Empty branch, create a new leaf
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    
                    let mut new_leaf = manager.acquire_node();
                    *new_leaf.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                    
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children: new_children, sizes: new_sizes } => {
                            new_children.push(Some(new_leaf));
                            *new_sizes = Some(vec![1]);
                        },
                        _ => unreachable!()
                    }
                    
                    (new_node, false, None)
                } else {
                    if let Some(first_child) = &children[0] {
                        // Try to add to the first child
                        let (new_child, was_split, overflow) = 
                            first_child.push_front(manager, value, shift - NODE_BITS);
                        
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: new_children, sizes: new_sizes } => {
                                // Copy children
                                *new_children = children.clone();
                                // Update first child
                                let new_child_clone = new_child.clone();
                                new_children[0] = Some(new_child_clone);
                                
                                // Handle overflow if split occurred
                                if was_split {
                                    if children.len() < NODE_SIZE {
                                        // Insert overflow at the beginning
                                        let overflow_clone = overflow.clone();
                                        new_children.insert(0, overflow_clone);
                                        
                                        // Update size table
                                        if let Some(old_sizes) = sizes {
                                            let mut new_size_table = Vec::with_capacity(new_children.len());
                                            let overflow_size = overflow.unwrap().size();
                                            new_size_table.push(overflow_size);
                                            
                                            for &size in old_sizes.iter() {
                                                new_size_table.push(size + overflow_size);
                                            }
                                            
                                            *new_sizes = Some(new_size_table);
                                        } else {
                                            // Convert to relaxed node
                                            let mut size_table = Vec::with_capacity(new_children.len());
                                            let mut sum = 0;
                                            
                                            for child in new_children.iter().filter_map(|c| c.clone()) {
                                                sum += child.size();
                                                size_table.push(sum);
                                            }
                                            
                                            *new_sizes = Some(size_table);
                                        }
                                        
                                        (new_node, false, None)
                                    } else {
                                        // Node is full, we need to split
                                        let mut overflow_node = manager.acquire_node();
                                        match overflow_node.get_mut().unwrap() {
                                            Node::Branch { children: overflow_children, sizes: overflow_sizes } => {
                                                let overflow_clone = overflow.clone();
                                                *overflow_children = vec![overflow_clone.clone()];
                                                *overflow_sizes = Some(vec![overflow_clone.unwrap().size()]);
                                            },
                                            _ => unreachable!()
                                        }
                                        
                                        (new_node, true, Some(overflow_node))
                                    }
                                } else {
                                    // No split, just update size table if needed
                                    if let Some(old_sizes) = sizes {
                                        let mut new_size_table = old_sizes.clone();
                                        let new_child_clone = new_child.clone();
                                        let size_inc = new_child_clone.size() - first_child.size();
                                        
                                        for size in new_size_table.iter_mut() {
                                            *size += size_inc;
                                        }
                                        
                                        *new_sizes = Some(new_size_table);
                                    }
                                    
                                    (new_node, false, None)
                                }
                            },
                            _ => unreachable!()
                        }
                    } else {
                        // Empty first slot, create a new leaf
                        let mut new_chunk = manager.acquire_chunk();
                        new_chunk.get_mut().unwrap().push_back(value);
                        
                        let mut new_leaf = manager.acquire_node();
                        *new_leaf.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                        
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: new_children, sizes: new_sizes } => {
                                // Copy children
                                *new_children = children.clone();
                                // Set the first child
                                new_children[0] = Some(new_leaf.clone());
                                
                                // Update size table
                                if let Some(old_sizes) = sizes {
                                    let mut new_size_table = old_sizes.clone();
                                    let leaf_size = new_leaf.size();
                                    
                                    for i in 0..new_size_table.len() {
                                        new_size_table[i] += leaf_size;
                                    }
                                    
                                    *new_sizes = Some(new_size_table);
                                } else {
                                    // Convert to relaxed node
                                    let mut size_table = Vec::with_capacity(children.len());
                                    let mut sum = new_leaf.size();
                                    size_table.push(sum);
                                    
                                    for i in 1..children.len() {
                                        if let Some(child) = &children[i] {
                                            sum += child.size();
                                        }
                                        size_table.push(sum);
                                    }
                                    
                                    *new_sizes = Some(size_table);
                                }
                            },
                            _ => unreachable!()
                        }
                        
                        (new_node, false, None)
                    }
                }
            }
        }
    }
    
    /// Join two nodes at the same level to create a new node.
    ///
    /// This is used for concatenation operations.
    pub fn join(&self, 
                manager: &MemoryManager<T>,
                other: &Node<T>,
                shift: usize) -> ManagedRef<Node<T>> {
        match (self, other) {
            (Node::Leaf { elements: left }, Node::Leaf { elements: right }) => {
                let left_len = left.len();
                let right_len = right.len();
                let total_len = left_len + right_len;
                
                if total_len <= CHUNK_SIZE {
                    // We can fit everything in a single leaf
                    let mut new_chunk = left.clone();
                    match new_chunk.make_mut() {
                        Ok(chunk) => {
                            // Append elements from right chunk
                            for i in 0..right_len {
                                if let Some(value) = right.get(i) {
                                    chunk.push_back(value.clone());
                                }
                            }
                        },
                        Err(mut new_managed) => {
                            let chunk = new_managed.get_mut().unwrap();
                            // Append elements from right chunk
                            for i in 0..right_len {
                                if let Some(value) = right.get(i) {
                                    chunk.push_back(value.clone());
                                }
                            }
                            new_chunk = new_managed;
                        }
                    }
                    
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = Node::Leaf { elements: new_chunk };
                    new_node
                } else {
                    // Need to create a branch node
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children, sizes } => {
                            let mut left_node = manager.acquire_node();
                            *left_node.get_mut().unwrap() = Node::Leaf { elements: left.clone() };
                            
                            let mut right_node = manager.acquire_node();
                            *right_node.get_mut().unwrap() = Node::Leaf { elements: right.clone() };
                            
                            children.push(Some(left_node));
                            children.push(Some(right_node));
                            
                            *sizes = Some(vec![left_len, total_len]);
                        },
                        _ => unreachable!()
                    }
                    
                    new_node
                }
            },
            (Node::Branch { children: left_children, sizes: left_sizes },
             Node::Branch { children: right_children, sizes: right_sizes }) => {
                // Combine two branch nodes
                let left_child_count = left_children.len();
                let right_child_count = right_children.len();
                let total_children = left_child_count + right_child_count;
                
                let left_size = self.size();
                let total_size = left_size + other.size();
                
                if total_children <= NODE_SIZE {
                    // We can fit all children in a single node
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
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
                            let mut size_table = Vec::with_capacity(total_children);
                            
                            if let (Some(left_sizes), Some(right_sizes)) = (left_sizes, right_sizes) {
                                // Both nodes are relaxed
                                for &size in left_sizes.iter() {
                                    size_table.push(size);
                                }
                                
                                for &size in right_sizes.iter() {
                                    size_table.push(left_size + size);
                                }
                            } else if let Some(left_sizes) = left_sizes {
                                // Left node is relaxed
                                for &size in left_sizes.iter() {
                                    size_table.push(size);
                                }
                                
                                let mut sum = left_size;
                                for child in right_children.iter().filter_map(|c| c.as_ref()) {
                                    sum += child.size();
                                    size_table.push(sum);
                                }
                            } else if let Some(right_sizes) = right_sizes {
                                // Right node is relaxed
                                let mut sum = 0;
                                for child in left_children.iter().filter_map(|c| c.as_ref()) {
                                    sum += child.size();
                                    size_table.push(sum);
                                }
                                
                                for &size in right_sizes.iter() {
                                    size_table.push(left_size + size);
                                }
                            } else {
                                // Neither node is relaxed
                                let mut sum = 0;
                                
                                // Calculate sizes for left children
                                for child in left_children.iter().filter_map(|c| c.as_ref()) {
                                    sum += child.size();
                                    size_table.push(sum);
                                }
                                
                                // Calculate sizes for right children
                                for child in right_children.iter().filter_map(|c| c.as_ref()) {
                                    sum += child.size();
                                    size_table.push(sum);
                                }
                            }
                            *sizes = Some(size_table);
                        },
                        _ => unreachable!()
                    }
                    new_node
                } else {
                    // Too many children, need to create a higher-level node
                    let mut new_left = manager.acquire_node();
                    match new_left.get_mut().unwrap() {
                        Node::Branch { children, sizes } => {
                            *children = left_children.clone();
                            *sizes = left_sizes.clone();
                        },
                        _ => unreachable!()
                    }

                    let mut new_right = manager.acquire_node();
                    match new_right.get_mut().unwrap() {
                        Node::Branch { children, sizes } => {
                            *children = right_children.clone();
                            *sizes = right_sizes.clone();
                        },
                        _ => unreachable!()
                    }

                    // Create a new parent node
                    let mut parent = manager.acquire_node();
                    match parent.get_mut().unwrap() {
                        Node::Branch { children, sizes } => {
                            children.push(Some(new_left));
                            children.push(Some(new_right));
                            *sizes = Some(vec![left_size, total_size]);
                        },
                        _ => unreachable!()
                    }

                    parent
                }
            },
            (leaf @ Node::Leaf { .. }, branch @ Node::Branch { .. }) => {
                // Convert leaf to branch and join
                let mut new_left = manager.acquire_node();
                *new_left.get_mut().unwrap() = leaf.clone();

                let mut branch_node = manager.acquire_node();
                match branch_node.get_mut().unwrap() {
                    Node::Branch { children, sizes } => {
                        children.push(Some(new_left));
                        *sizes = Some(vec![leaf.size()]);
                    },
                    _ => unreachable!()
                }

                branch_node.join(manager, branch, shift)
            },
            (branch @ Node::Branch { .. }, leaf @ Node::Leaf { .. }) => {
                // Convert leaf to branch and join
                let mut new_right = manager.acquire_node();
                *new_right.get_mut().unwrap() = leaf.clone();

                let mut branch_node = manager.acquire_node();
                match branch_node.get_mut().unwrap() {
                    Node::Branch { children, sizes } => {
                        children.push(Some(new_right));
                        *sizes = Some(vec![leaf.size()]);
                    },
                    _ => unreachable!()
                }

                branch.join(manager, &branch_node, shift)
            }
        }
    }

    /// Split this node at the given index, returning left and right parts.
    pub fn split(&self, 
                 manager: &MemoryManager<T>, 
                 index: usize, 
                 shift: usize) -> (ManagedRef<Node<T>>, ManagedRef<Node<T>>) {
        match self {
            Node::Leaf { elements } => {
                if index == 0 {
                    // Split before the first element
                    let mut empty = manager.acquire_node();
                    *empty.get_mut().unwrap() = Node::Leaf { elements: manager.acquire_chunk() };

                    let mut node = manager.acquire_node();
                    *node.get_mut().unwrap() = self.clone();

                    (empty, node)
                } else if index >= elements.len() {
                    // Split after the last element
                    let mut node = manager.acquire_node();
                    *node.get_mut().unwrap() = self.clone();

                    let mut empty = manager.acquire_node();
                    *empty.get_mut().unwrap() = Node::Leaf { elements: manager.acquire_chunk() };

                    (node, empty)
                } else {
                    // Split in the middle
                    let mut left_chunk = elements.clone();
                    let right_chunk;

                    match left_chunk.make_mut() {
                        Ok(chunk) => {
                            let mut right_elements = manager.acquire_chunk();

                            // Move elements after index to right chunk
                            for i in index..elements.len() {
                                if let Some(value) = chunk.get(i) {
                                    right_elements.get_mut().unwrap().push_back(value.clone());
                                }
                            }

                            // Truncate left chunk
                            while chunk.len() > index {
                                chunk.pop_back();
                            }

                            right_chunk = right_elements;
                        },
                        Err(mut new_left) => {
                            let left_elements = new_left.get_mut().unwrap();
                            let mut right_elements = manager.acquire_chunk();

                            // Move elements after index to right chunk
                            for i in index..elements.len() {
                                if let Some(value) = elements.get(i) {
                                    right_elements.get_mut().unwrap().push_back(value.clone());
                                }
                            }

                            // Truncate left chunk
                            while left_elements.len() > index {
                                left_elements.pop_back();
                            }

                            left_chunk = new_left;
                            right_chunk = right_elements;
                        }
                    }

                    let mut left_node = manager.acquire_node();
                    *left_node.get_mut().unwrap() = Node::Leaf { elements: left_chunk };

                    let mut right_node = manager.acquire_node();
                    *right_node.get_mut().unwrap() = Node::Leaf { elements: right_chunk };

                    (left_node, right_node)
                }
            },
            Node::Branch { children, sizes } => {
                if index == 0 {
                    // Split before the first element
                    let mut empty = manager.acquire_node();
                    *empty.get_mut().unwrap() = Node::Branch {
                        children: Vec::new(),
                        sizes: Some(Vec::new()),
                    };

                    let mut node = manager.acquire_node();
                    *node.get_mut().unwrap() = self.clone();

                    (empty, node)
                } else if index >= self.size() {
                    // Split after the last element
                    let mut node = manager.acquire_node();
                    *node.get_mut().unwrap() = self.clone();

                    let mut empty = manager.acquire_node();
                    *empty.get_mut().unwrap() = Node::Branch {
                        children: Vec::new(),
                        sizes: Some(Vec::new()),
                    };

                    (node, empty)
                } else {
                    // Find the child containing the split point
                    let (child_index, sub_index) = if let Some(sizes) = sizes {
                        // For relaxed nodes, binary search the size table
                        let mut idx = 0;
                        let mut left = 0;
                        let mut right = sizes.len();

                        while left < right {
                            let mid = left + (right - left) / 2;
                            if mid < sizes.len() && sizes[mid] <= index {
                                left = mid + 1;
                                idx = mid;
                            } else {
                                right = mid;
                            }
                        }

                        let prev_size = if idx > 0 { sizes[idx - 1] } else { 0 };
                        (idx, index - prev_size)
                    } else {
                        // For regular nodes, use bit operations
                        let child_index = (index >> shift) & NODE_MASK;
                        let sub_index = index & ((1 << shift) - 1);
                        (child_index, sub_index)
                    };

                    if child_index >= children.len() || children[child_index].is_none() {
                        // This shouldn't happen with a valid tree
                        panic!("Invalid tree structure in split operation");
                    }

                    let child = children[child_index].as_ref().unwrap();

                    // Split the child
                    let (child_left, child_right) = child.split(manager, sub_index, shift - NODE_BITS);

                    // Create left branch with children up to and including child_left
                    let mut left_node = manager.acquire_node();
                    match left_node.get_mut().unwrap() {
                        Node::Branch { children: left_children, sizes: left_sizes } => {
                            for i in 0..child_index {
                                left_children.push(children[i].clone());
                            }
                            left_children.push(Some(child_left.clone()));

                            // Create size table for left node
                            let mut left_size_table = Vec::with_capacity(child_index + 1);
                            if let Some(sizes) = sizes {
                                // Copy sizes for children before the split
                                for i in 0..child_index {
                                    left_size_table.push(sizes[i]);
                                }
                                
                                // Add size for the split child
                                left_size_table.push(
                                    (if child_index > 0 { sizes[child_index - 1] } else { 0 }) + 
                                    child_left.size()
                                );
                            } else {
                                // Calculate sizes
                                let mut sum = 0;
                                for i in 0..child_index {
                                    if let Some(child) = &children[i] {
                                        sum += child.size();
                                    }
                                    left_size_table.push(sum);
                                }
                                sum += child_left.size();
                                left_size_table.push(sum);
                            }

                            *left_sizes = Some(left_size_table);
                        },
                        _ => unreachable!()
                    }

                    // Create right branch with child_right and remaining children
                    let mut right_node = manager.acquire_node();
                    match right_node.get_mut().unwrap() {
                        Node::Branch { children: right_children, sizes: right_sizes } => {
                            right_children.push(Some(child_right.clone()));

                            for i in (child_index + 1)..children.len() {
                                right_children.push(children[i].clone());
                            }

                            // Create size table for right node
                            let mut right_size_table = Vec::with_capacity(children.len() - child_index);
                            let mut right_sum = child_right.size();
                            right_size_table.push(right_sum);

                            for i in (child_index + 1)..children.len() {
                                if let Some(child) = &children[i] {
                                    right_sum += child.size();
                                    right_size_table.push(right_sum);
                                }
                            }

                            *right_sizes = Some(right_size_table);
                        },
                        _ => unreachable!()
                    }

                    (left_node, right_node)
                }
            }
        }
    }

    /// Pop an element from the front of this node.
    pub fn pop_front(&self, 
                     manager: &MemoryManager<T>, 
                     shift: usize) -> (ManagedRef<Node<T>>, Option<T>) {
        match self {
            Node::Leaf { elements } => {
                if elements.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let mut new_elements = elements.clone();
                let result;

                match new_elements.make_mut() {
                    Ok(chunk) => {
                        result = chunk.pop_front();
                    },
                    Err(mut new_chunk) => {
                        result = new_chunk.get_mut().unwrap().pop_front();
                        new_elements = new_chunk;
                    }
                }

                let mut new_node = manager.acquire_node();
                *new_node.get_mut().unwrap() = Node::Leaf { elements: new_elements };

                (new_node, result)
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                // Try to get the first child
                if let Some(first_child) = &children[0] {
                    let (new_first_child, result) = first_child.pop_front(manager, shift - NODE_BITS);
                    
                    // If we got a result, update the first child and return
                    if result.is_some() {
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: node_children, sizes: node_sizes } => {
                                // Update the first child
                                let new_first_child_clone = new_first_child.clone();
                                node_children.push(Some(new_first_child_clone));
                                
                                // Copy the rest of the children
                                for i in 1..children.len() {
                                    node_children.push(children[i].clone());
                                }
                                
                                // Update sizes if needed
                                if let Some(old_sizes) = sizes {
                                    // Create a new size table
                                    let mut new_sizes_vec = Vec::with_capacity(old_sizes.len());
                                    let size_diff = first_child.size() - new_first_child.size();
                                    
                                    for &size in old_sizes.iter() {
                                        new_sizes_vec.push(size - size_diff);
                                    }
                                    
                                    *node_sizes = Some(new_sizes_vec);
                                } else {
                                    *node_sizes = None; // Regular nodes don't need a size table
                                }
                            },
                            _ => unreachable!()
                        }
                        
                        return (new_node, result);
                    }
                    
                    // If no result, remove the first child and continue
                    // Only do this if there are other children
                    if children.len() > 1 {
                        let mut new_node = manager.acquire_node();
                        match new_node.get_mut().unwrap() {
                            Node::Branch { children: node_children, sizes: node_sizes } => {
                                // Skip the first child
                                for i in 1..children.len() {
                                    node_children.push(children[i].clone());
                                }
                                
                                // Update size table
                                if let Some(old_sizes) = sizes {
                                    let mut new_size_table = Vec::with_capacity(old_sizes.len() - 1);
                                    let first_size = if old_sizes.is_empty() { 0 } else { old_sizes[0] };
                                    
                                    for i in 1..old_sizes.len() {
                                        new_size_table.push(old_sizes[i] - first_size);
                                    }
                                    
                                    *node_sizes = Some(new_size_table);
                                } else {
                                    *node_sizes = None;
                                }
                            },
                            _ => unreachable!()
                        }

                        // Try again with the new node
                        return new_node.pop_front(manager, shift);
                    }
                }
                
                // If we got here, either:
                // 1. The first child is None
                // 2. There's only one child and it's empty
                
                // Create an empty branch node
                let mut new_node = manager.acquire_node();
                *new_node.get_mut().unwrap() = Node::Branch {
                    children: Vec::new(),
                    sizes: Some(Vec::new()),
                };
                
                return (new_node, None);
            }
        }
    }

    /// Pop an element from the back of this node.
    pub fn pop_back(&self, 
                    manager: &MemoryManager<T>, 
                    shift: usize) -> (ManagedRef<Node<T>>, Option<T>) {
        match self {
            Node::Leaf { elements } => {
                if elements.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let mut new_elements = elements.clone();
                let result;

                match new_elements.make_mut() {
                    Ok(chunk) => {
                        result = chunk.pop_back();
                    },
                    Err(mut new_chunk) => {
                        result = new_chunk.get_mut().unwrap().pop_back();
                        new_elements = new_chunk;
                    }
                }

                let mut new_node = manager.acquire_node();
                *new_node.get_mut().unwrap() = Node::Leaf { elements: new_elements };

                (new_node, result)
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let last_idx = children.len() - 1;

                // Try to pop from the last child
                if let Some(last_child) = &children[last_idx] {
                    let (new_child, result) = last_child.pop_back(manager, shift - NODE_BITS);

                    if result.is_none() {
                        // Last child is empty, remove it if there are other children
                        if children.len() > 1 {
                            let mut new_node = manager.acquire_node();
                            match new_node.get_mut().unwrap() {
                                Node::Branch { children: node_children, sizes: node_sizes } => {
                                    // Skip the last child
                                    for i in 0..last_idx {
                                        node_children.push(children[i].clone());
                                    }
                                
                                // Update size table
                                    if let Some(old_sizes) = sizes {
                                        let mut new_size_table = Vec::with_capacity(last_idx);
                                    
                                        // Just use the sizes up to the last child
                                        for i in 0..last_idx {
                                            new_size_table.push(old_sizes[i]);
                                        }
                                    
                                        *node_sizes = Some(new_size_table);
                                    } else {
                                        *node_sizes = None;
                                    }
                                },
                                _ => unreachable!()
                            }

                            // Try popping from the new last child
                            return new_node.pop_back(manager, shift);
                        } else {
                            // No other children, return empty branch
                            let mut new_node = manager.acquire_node();
                            *new_node.get_mut().unwrap() = Node::Branch {
                                children: Vec::new(),
                                sizes: Some(Vec::new()),
                            };

                            return (new_node, None);
                        }
                    }

                    // Create a new branch with the updated last child
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children: new_children, sizes: new_sizes } => {
                            // Copy children up to the last one
                            for i in 0..last_idx {
                                new_children.push(children[i].clone());
                            }

                            // Add the updated last child
                            let new_child_clone = new_child.clone();
                            new_children.push(Some(new_child_clone));

                            // Update size table
                            if let Some(old_sizes) = sizes {
                                let size_diff = last_child.size() - new_child.size();
                                let mut new_size_table = Vec::with_capacity(children.len());
                            
                                for i in 0..last_idx {
                                    new_size_table.push(old_sizes[i]);
                                }
                            
                                // Update the last size
                                new_size_table.push(old_sizes[last_idx] - size_diff);
                            
                                *new_sizes = Some(new_size_table);
                            } else {
                                // For regular nodes, just keep it as None
                                *new_sizes = None;
                            }
                        },
                        _ => unreachable!()
                    }

                    (new_node, result)
                } else {
                    // Last child is None, try previous child
                    let mut new_node = manager.acquire_node();
                    match new_node.get_mut().unwrap() {
                        Node::Branch { children: node_children, sizes: node_sizes } => {
                            // Skip the last child
                            for i in 0..last_idx {
                                node_children.push(children[i].clone());
                            }

                            // Update size table
                            if let Some(old_sizes) = sizes {
                                let mut new_size_table = Vec::with_capacity(last_idx);
                                
                                // Just use the sizes up to the last child
                                for i in 0..last_idx {
                                    new_size_table.push(old_sizes[i]);
                                }
                            
                                *node_sizes = Some(new_size_table);
                            } else {
                                *node_sizes = None;
                            }
                        },
                        _ => unreachable!()
                    }

                    // Try popping from the new last child
                    if new_node.child_count() > 0 {
                        return new_node.pop_back(manager, shift);
                    } else {
                        // No children left
                        (new_node, None)
                    }
                }
            }
        }
    }
}

impl<T: Clone + Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Leaf { elements } => {
                f.debug_struct("Leaf")
                    .field("elements", elements)
                    .field("size", &elements.len())
                    .finish()
            },
            Node::Branch { children, sizes } => {
                let mut debug_struct = f.debug_struct("Branch");

                debug_struct.field("size", &self.size());
                debug_struct.field("child_count", &self.child_count());

                if let Some(sizes) = sizes {
                    debug_struct.field("relaxed", &true);
                    debug_struct.field("sizes", sizes);
                } else {
                    debug_struct.field("relaxed", &false);
                }

                debug_struct.field("children", children);
                debug_struct.finish()
            }
        }
    }
}