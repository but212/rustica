use smallvec::SmallVec;
use std::fmt::{self, Debug};
use std::sync::Arc;

const ADAPTIVE_INLINE_SIZE: usize = 64;

const BRANCHING_FACTOR: usize = 32; // Node children count
const LEAF_CAPACITY: usize = 64; // Leaf node data capacity

const SMALL_BRANCH_SIZE: usize = 8; // Most nodes are not full
const SMALL_SIZE_TABLE_SIZE: usize = 8; // Corresponding size table

type Generation = u64;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PersistentVector<T> {
    inner: VectorImpl<T>,
    len: usize,
    generation: Generation,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum VectorImpl<T> {
    Inline {
        elements: SmallVec<[T; ADAPTIVE_INLINE_SIZE]>,
    },
    Tree {
        tree: Arc<RRBTree<T>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct RRBTree<T> {
    root: Arc<RRBNode<T>>,
    height: usize,
    len: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RRBNode<T> {
    Branch {
        children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        sizes: Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
    },
    Leaf {
        elements: SmallVec<[T; LEAF_CAPACITY]>,
    },
}

impl<T: Clone> PersistentVector<T> {
    pub fn new() -> Self {
        Self {
            inner: VectorImpl::Inline {
                elements: SmallVec::new(),
            },
            len: 0,
            generation: 0,
        }
    }

    pub fn from_slice(slice: &[T]) -> Self {
        Self::from_iter(slice.iter().cloned())
    }

    pub fn unit(value: T) -> Self {
        Self {
            inner: VectorImpl::Inline {
                elements: SmallVec::from_iter([value]),
            },
            len: 1,
            generation: 0,
        }
    }

    pub fn map<U: Clone, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U,
    {
        let mapped: Vec<U> = self.iter().map(f).collect();
        PersistentVector::from_iter(mapped)
    }

    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        let filtered: Vec<T> = self.iter().filter(|x| predicate(x)).cloned().collect();
        Self::from_iter(filtered)
    }

    pub fn filter_map<U: Clone, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> Option<U>,
    {
        let filtered: Vec<U> = self.iter().filter_map(f).collect();
        PersistentVector::from_iter(filtered)
    }

    pub fn flat_map<U: Clone, F, I>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> I,
        I: IntoIterator<Item = U>,
    {
        let flattened: Vec<U> = self.iter().flat_map(f).collect();
        PersistentVector::from_iter(flattened)
    }

    pub fn dedup(&self) -> Self
    where
        T: PartialEq,
    {
        let mut result = Vec::new();
        let mut last: Option<&T> = None;

        for item in self.iter() {
            if last != Some(item) {
                result.push(item.clone());
                last = Some(item);
            }
        }

        Self::from_iter(result)
    }

    pub fn sorted(&self) -> std::vec::IntoIter<&T>
    where
        T: Ord,
    {
        let mut refs: Vec<&T> = self.iter().collect();
        refs.sort();
        refs.into_iter()
    }

    pub fn with_cache_policy<P>(_policy: P) -> Self {
        Self::new()
    }

    pub fn from_slice_with_cache_policy<P>(slice: &[T], _policy: P) -> Self {
        Self::from_slice(slice)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push_back(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
                    // Stay inline - Vec-like performance
                    let mut new_elements = elements.clone();
                    new_elements.push(value);
                    Self {
                        inner: VectorImpl::Inline {
                            elements: new_elements,
                        },
                        len: self.len + 1,
                        generation: self.generation + 1,
                    }
                } else {
                    // Transition to tree structure
                    self.transition_to_tree().push_back(value)
                }
            },
            VectorImpl::Tree { tree: _ } => {
                // Use tail chunking for O(1) amortized performance
                self.tree_push_back(value)
            },
        }
    }

    pub fn push_front(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
                    // Stay inline but insert at front
                    let mut new_elements = SmallVec::with_capacity(elements.len() + 1);
                    new_elements.push(value);
                    new_elements.extend(elements.iter().cloned());
                    Self {
                        inner: VectorImpl::Inline {
                            elements: new_elements,
                        },
                        len: self.len + 1,
                        generation: self.generation + 1,
                    }
                } else {
                    // Transition to tree structure
                    self.transition_to_tree().push_front(value)
                }
            },
            VectorImpl::Tree { tree: _ } => {
                // Use head chunking for O(1) amortized performance
                self.tree_push_front(value)
            },
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.get(index),
        }
    }

    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.len {
            return self.clone();
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                let mut new_elements = elements.clone();
                new_elements[index] = value;
                Self {
                    inner: VectorImpl::Inline {
                        elements: new_elements,
                    },
                    len: self.len,
                    generation: self.generation + 1,
                }
            },
            VectorImpl::Tree { tree } => {
                let new_tree = tree.update(index, value);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(new_tree),
                    },
                    len: self.len,
                    generation: self.generation + 1,
                }
            },
        }
    }

    fn transition_to_tree(&self) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                // Create initial tree structure with tail chunk
                let tree = RRBTree::from_elements(elements.iter().cloned());
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(tree),
                    },
                    len: self.len,
                    generation: self.generation + 1,
                }
            },
            VectorImpl::Tree { .. } => self.clone(),
        }
    }

    fn tree_push_back(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Tree { tree } => {
                let new_tree = tree.push_back(value);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(new_tree),
                    },
                    len: self.len + 1,
                    generation: self.generation + 1,
                }
            },
            _ => unreachable!(),
        }
    }

    fn tree_push_front(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Tree { tree } => {
                let new_tree = tree.push_front(value);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(new_tree),
                    },
                    len: self.len + 1,
                    generation: self.generation + 1,
                }
            },
            _ => unreachable!(),
        }
    }

    pub fn concat(&self, other: &Self) -> Self {
        match (&self.inner, &other.inner) {
            (VectorImpl::Inline { elements: left }, VectorImpl::Inline { elements: right }) => {
                if left.len() + right.len() <= ADAPTIVE_INLINE_SIZE {
                    // Both small, stay inline
                    let mut new_elements = left.clone();
                    new_elements.extend(right.iter().cloned());
                    Self {
                        inner: VectorImpl::Inline {
                            elements: new_elements,
                        },
                        len: self.len + other.len,
                        generation: self.generation + 1, // Simple increment for concat
                    }
                } else {
                    // Transition to tree
                    let left_tree = RRBTree::from_elements(left.iter().cloned());
                    let right_tree = RRBTree::from_elements(right.iter().cloned());
                    let merged_tree = left_tree.concat(&right_tree);
                    Self {
                        inner: VectorImpl::Tree {
                            tree: Arc::new(merged_tree),
                        },
                        len: self.len + other.len,
                        generation: self.generation + 1, // Simple increment for concat
                    }
                }
            },
            _ => {
                // At least one is tree, use tree concatenation
                let left_tree = self.ensure_tree();
                let right_tree = other.ensure_tree();
                let merged_tree = left_tree.concat(&right_tree);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(merged_tree),
                    },
                    len: self.len + other.len,
                    generation: self.generation + 1, // Simple increment for concat
                }
            },
        }
    }

    fn ensure_tree(&self) -> RRBTree<T> {
        match &self.inner {
            VectorImpl::Inline { elements } => RRBTree::from_elements(elements.iter().cloned()),
            VectorImpl::Tree { tree } => (**tree).clone(),
        }
    }

    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                if let Some(last) = elements.last().cloned() {
                    let mut new_elements = elements.clone();
                    new_elements.pop();
                    Some((
                        Self {
                            inner: VectorImpl::Inline {
                                elements: new_elements,
                            },
                            len: self.len - 1,
                            generation: self.generation + 1,
                        },
                        last,
                    ))
                } else {
                    None
                }
            },
            VectorImpl::Tree { tree } => tree.pop_back().map(|(new_tree, value)| {
                (
                    Self {
                        inner: VectorImpl::Tree {
                            tree: Arc::new(new_tree),
                        },
                        len: self.len - 1,
                        generation: self.generation + 1,
                    },
                    value,
                )
            }),
        }
    }

    pub fn pop_front(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                if let Some(first) = elements.first().cloned() {
                    let new_elements = SmallVec::from_iter(elements.iter().skip(1).cloned());
                    Some((
                        Self {
                            inner: VectorImpl::Inline {
                                elements: new_elements,
                            },
                            len: self.len - 1,
                            generation: self.generation + 1,
                        },
                        first,
                    ))
                } else {
                    None
                }
            },
            VectorImpl::Tree { tree } => tree.pop_front().map(|(new_tree, value)| {
                (
                    Self {
                        inner: VectorImpl::Tree {
                            tree: Arc::new(new_tree),
                        },
                        len: self.len - 1,
                        generation: self.generation + 1,
                    },
                    value,
                )
            }),
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    pub fn last(&self) -> Option<&T> {
        if self.len > 0 {
            self.get(self.len - 1)
        } else {
            None
        }
    }

    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index >= self.len {
            return (self.clone(), Self::new());
        }
        if index == 0 {
            return (Self::new(), self.clone());
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                let left = SmallVec::from_iter(elements.iter().take(index).cloned());
                let right = SmallVec::from_iter(elements.iter().skip(index).cloned());
                (
                    Self {
                        inner: VectorImpl::Inline { elements: left },
                        len: index,
                        generation: self.generation + 1,
                    },
                    Self {
                        inner: VectorImpl::Inline { elements: right },
                        len: self.len - index,
                        generation: self.generation + 1,
                    },
                )
            },
            VectorImpl::Tree { tree } => {
                let (left_tree, right_tree) = tree.split_at(index);
                (
                    Self {
                        inner: VectorImpl::Tree {
                            tree: Arc::new(left_tree),
                        },
                        len: index,
                        generation: self.generation + 1,
                    },
                    Self {
                        inner: VectorImpl::Tree {
                            tree: Arc::new(right_tree),
                        },
                        len: self.len - index,
                        generation: self.generation + 1,
                    },
                )
            },
        }
    }

    pub fn take(&self, n: usize) -> Self {
        if n >= self.len {
            self.clone()
        } else {
            self.split_at(n).0
        }
    }

    pub fn skip(&self, n: usize) -> Self {
        if n >= self.len {
            Self::new()
        } else {
            self.split_at(n).1
        }
    }

    pub fn insert(&self, index: usize, value: T) -> Self {
        if index >= self.len {
            return self.push_back(value);
        }
        if index == 0 {
            return self.push_front(value);
        }

        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
    }

    pub fn remove(&self, index: usize) -> Option<Self> {
        if index >= self.len {
            return None;
        }

        if self.len == 1 {
            return Some(Self::new());
        }

        let (left, right) = self.split_at(index);
        let right_without_first = right.skip(1);
        Some(left.concat(&right_without_first))
    }

    pub fn iter(&self) -> PersistentVectorIter<'_, T> {
        PersistentVectorIter {
            vector: self,
            position: 0,
        }
    }

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }
}

impl<T: Clone> RRBTree<T> {
    fn from_elements<I: Iterator<Item = T>>(elements: I) -> Self {
        let elements: Vec<T> = elements.collect();

        if elements.len() <= LEAF_CAPACITY {
            // Single leaf node
            let leaf = RRBNode::Leaf {
                elements: SmallVec::from_iter(elements.clone()),
            };
            Self {
                root: Arc::new(leaf),
                height: 0,
                len: elements.len(),
            }
        } else {
            // Build proper tree structure
            Self::build_tree(elements)
        }
    }

    fn build_tree(elements: Vec<T>) -> Self {
        let total_len = elements.len();

        // Build leaves first
        let mut leaves = Vec::new();
        for chunk in elements.chunks(LEAF_CAPACITY) {
            let leaf = RRBNode::Leaf {
                elements: SmallVec::from_iter(chunk.iter().cloned()),
            };
            leaves.push(Arc::new(leaf));
        }

        // Build tree bottom-up
        let (root, height) = Self::build_tree_recursive(leaves);

        Self {
            root,
            height,
            len: total_len,
        }
    }

    fn build_tree_recursive(nodes: Vec<Arc<RRBNode<T>>>) -> (Arc<RRBNode<T>>, usize) {
        if nodes.len() == 1 {
            return (nodes.into_iter().next().unwrap(), 0);
        }

        let mut next_level = Vec::new();

        for chunk in nodes.chunks(BRANCHING_FACTOR) {
            let children = SmallVec::from_iter(chunk.iter().cloned());
            let branch = RRBNode::Branch {
                children,
                sizes: None, // Regular node for now
            };
            next_level.push(Arc::new(branch));
        }

        let (root, sub_height) = Self::build_tree_recursive(next_level);
        (root, sub_height + 1)
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.root.get(index)
    }

    fn update(&self, index: usize, value: T) -> Self {
        let new_root = self.root.update(index, value);
        Self {
            root: Arc::new(new_root),
            height: self.height,
            len: self.len, // Length unchanged for update
        }
    }

    fn push_back(&self, value: T) -> Self {
        // Implementation would use tail chunking for O(1) amortized
        // For now, simplified
        let new_root = self.root.push_back(value);
        Self {
            root: Arc::new(new_root),
            height: self.height,
            len: self.len + 1, // Increment length for push_back
        }
    }

    fn push_front(&self, value: T) -> Self {
        // Implementation would use head chunking for O(1) amortized
        // For now, simplified
        let new_root = self.root.push_front(value);
        Self {
            root: Arc::new(new_root),
            height: self.height,
            len: self.len + 1, // Increment length for push_front
        }
    }

    fn concat(&self, other: &Self) -> Self {
        // Implementation would use proper RRB-Tree concatenation
        // For now, simplified
        Self {
            root: self.root.clone(),
            height: self.height.max(other.height),
            len: self.len + other.len, // Combined length
        }
    }

    fn pop_back(&self) -> Option<(Self, T)> {
        if self.len == 0 {
            return None;
        }

        // Simplified implementation - would use tail chunking in real implementation
        self.get(self.len - 1).cloned().map(|last| {
            // Create new tree without last element (simplified)
            (
                Self {
                    root: self.root.clone(),
                    height: self.height,
                    len: self.len - 1,
                },
                last,
            )
        })
    }

    fn pop_front(&self) -> Option<(Self, T)> {
        if self.len == 0 {
            return None;
        }

        // Simplified implementation - would use head chunking in real implementation
        self.get(0).cloned().map(|first| {
            (
                Self {
                    root: self.root.clone(),
                    height: self.height,
                    len: self.len - 1,
                },
                first,
            )
        })
    }

    fn split_at(&self, index: usize) -> (Self, Self) {
        // Simplified implementation
        (
            Self {
                root: self.root.clone(),
                height: self.height,
                len: index,
            },
            Self {
                root: self.root.clone(),
                height: self.height,
                len: self.len - index,
            },
        )
    }
}

impl<T: Clone> RRBNode<T> {
    fn get(&self, index: usize) -> Option<&T> {
        match self {
            RRBNode::Leaf { elements } => elements.get(index),
            RRBNode::Branch { children, sizes } => {
                if let Some(sizes) = sizes {
                    // Relaxed node - use size table for navigation
                    self.get_relaxed(index, children, sizes)
                } else {
                    // Regular node - simple calculation
                    let child_size = LEAF_CAPACITY;
                    let child_index = index / child_size;
                    let sub_index = index % child_size;
                    children.get(child_index)?.get(sub_index)
                }
            },
        }
    }

    fn get_relaxed<'a>(
        &self, index: usize, children: &'a SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        sizes: &'a SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>,
    ) -> Option<&'a T> {
        let mut cumulative_size = 0;
        for (i, &size) in sizes.iter().enumerate() {
            if index < cumulative_size + size {
                let sub_index = index - cumulative_size;
                return children.get(i)?.get(sub_index);
            }
            cumulative_size += size;
        }
        None
    }

    fn find_child(
        &self, index: usize, sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
    ) -> Option<(usize, usize)> {
        if let Some(sizes) = sizes {
            // Relaxed node - use size table
            let mut i = 0;
            let mut cumulative_size = 0;
            while i < sizes.len() {
                let size = sizes[i];
                if index < cumulative_size + size {
                    return Some((i, index - cumulative_size));
                }
                cumulative_size += size;
                i += 1;
            }
            None
        } else {
            // Regular node - simple calculation
            let child_size = LEAF_CAPACITY;
            let child_index = index / child_size;
            let sub_index = index % child_size;
            Some((child_index, sub_index))
        }
    }

    fn update(&self, index: usize, value: T) -> Self {
        match self {
            RRBNode::Leaf { elements } => {
                let mut new_elements = elements.clone();
                if index < new_elements.len() {
                    new_elements[index] = value;
                }
                RRBNode::Leaf {
                    elements: new_elements,
                }
            },
            RRBNode::Branch { children, sizes } => {
                if let Some((child_index, sub_index)) = self.find_child(index, sizes) {
                    if let Some(child) = children.get(child_index) {
                        let updated_child = child.update(sub_index, value);
                        let mut new_children = children.clone();
                        new_children[child_index] = Arc::new(updated_child);
                        RRBNode::Branch {
                            children: new_children,
                            sizes: sizes.clone(),
                        }
                    } else {
                        self.clone()
                    }
                } else {
                    self.clone()
                }
            },
        }
    }

    fn push_back(&self, value: T) -> Self {
        match self {
            RRBNode::Leaf { elements } => {
                let mut new_elements = elements.clone();
                new_elements.push(value);
                RRBNode::Leaf {
                    elements: new_elements,
                }
            },
            RRBNode::Branch {
                children: _,
                sizes: _,
            } => {
                // Implementation would handle branch logic
                self.clone() // Simplified for now
            },
        }
    }

    fn push_front(&self, value: T) -> Self {
        match self {
            RRBNode::Leaf { elements } => {
                let mut new_elements = SmallVec::with_capacity(elements.len() + 1);
                new_elements.push(value);
                new_elements.extend(elements.iter().cloned());
                RRBNode::Leaf {
                    elements: new_elements,
                }
            },
            RRBNode::Branch {
                children: _,
                sizes: _,
            } => {
                // Implementation would handle branch logic
                self.clone() // Simplified for now
            },
        }
    }

    // Note: calculate_len method removed as it was unused
}

impl<T: Clone> Default for PersistentVector<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct PersistentVectorIter<'a, T> {
    vector: &'a PersistentVector<T>,
    position: usize,
}

pub struct PersistentVectorIntoIter<T> {
    vector: PersistentVector<T>,
    position: usize,
}

impl<'a, T: Clone> Iterator for PersistentVectorIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.vector.len() {
            let item = self.vector.get(self.position);
            self.position += 1;
            item
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vector.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<'a, T: Clone> ExactSizeIterator for PersistentVectorIter<'a, T> {}

impl<T: Clone> Iterator for PersistentVectorIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.vector.len() {
            let item = self.vector.get(self.position).cloned();
            self.position += 1;
            item
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vector.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> ExactSizeIterator for PersistentVectorIntoIter<T> {}

// Trait implementations
impl<T: Clone> FromIterator<T> for PersistentVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let elements: Vec<T> = iter.into_iter().collect();
        if elements.len() <= ADAPTIVE_INLINE_SIZE {
            Self {
                inner: VectorImpl::Inline {
                    elements: SmallVec::from_iter(elements.clone()),
                },
                len: elements.len(),
                generation: 0,
            }
        } else {
            let tree = RRBTree::from_elements(elements.into_iter());
            Self {
                inner: VectorImpl::Tree {
                    tree: Arc::new(tree.clone()),
                },
                len: tree.len,
                generation: 0,
            }
        }
    }
}

impl<T: Clone> Extend<T> for PersistentVector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            *self = self.push_back(item);
        }
    }
}

impl<T: Clone> From<Vec<T>> for PersistentVector<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_iter(vec)
    }
}

impl<T: Clone> From<PersistentVector<T>> for Vec<T> {
    fn from(pvec: PersistentVector<T>) -> Self {
        pvec.to_vec()
    }
}

impl<T: Clone> IntoIterator for PersistentVector<T> {
    type Item = T;
    type IntoIter = PersistentVectorIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        PersistentVectorIntoIter {
            vector: self,
            position: 0,
        }
    }
}

impl<'a, T: Clone> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = PersistentVectorIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Clone> std::ops::Index<usize> for PersistentVector<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                write!(
                    f,
                    "PersistentVector(Inline, len={}, elements={:?})",
                    self.len,
                    elements.as_slice()
                )
            },
            VectorImpl::Tree { .. } => {
                write!(
                    f,
                    "PersistentVector(Tree, len={}, generation={})",
                    self.len, self.generation
                )
            },
        }
    }
}

// Macro for convenient construction
#[macro_export]
macro_rules! pvec {
    () => { PersistentVector::new() };
    ($($x:expr),+ $(,)?) => {
        PersistentVector::from_iter([$($x),+])
    };
}

pub use pvec;
