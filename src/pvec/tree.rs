//! Internal RRB tree implementation.
//!
//! This module contains the RRB (Relaxed Radix Balanced) tree that provides
//! the underlying data structure for efficient persistent vector operations.
//!
//! # Architecture
//!
//! The `RRBTree` structure uses a three-part design:
//!
//! ```text
//! ┌──────────┬─────────────────────────┬──────────┐
//! │   Head   │      Tree (root)        │   Tail   │
//! │  Buffer  │    (RRB structure)      │  Buffer  │
//! └──────────┴─────────────────────────┴──────────┘
//! ```

use super::node::{
    BRANCHING_FACTOR, LEAF_CAPACITY, RRBNode, SMALL_BRANCH_SIZE, SMALL_SIZE_TABLE_SIZE,
};
use smallvec::SmallVec;
use std::sync::Arc;

/// An RRB tree structure for efficient persistent vector operations.
///
/// The RRB tree combines the root tree structure with head and tail buffers
/// for optimal performance on common operations like `push_back` and `push_front`.
///
/// # Structure
///
/// - **Head buffer**: Stores up to `LEAF_CAPACITY` (64) elements at the front
/// - **Root**: The main tree structure containing the bulk of elements
/// - **Tail buffer**: Stores up to `LEAF_CAPACITY` (64) elements at the back
///
/// # Invariants
///
/// - `len` equals `head.len() + tree_size + tail.len()`
/// - `height` reflects the depth of the tree (0 for leaf-only)
/// - Buffers are flushed to the tree when they reach capacity
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RRBTree<T> {
    /// The root node of the tree structure.
    ///
    /// May be an empty leaf if all elements are in head/tail buffers.
    pub root: Arc<RRBNode<T>>,
    /// Tail buffer for efficient back insertions.
    ///
    /// Elements are accumulated here until the buffer is full,
    /// then flushed to the tree as a new leaf node.
    pub tail: SmallVec<[T; LEAF_CAPACITY]>,
    /// Head buffer for efficient front insertions.
    ///
    /// Elements are accumulated here until the buffer is full,
    /// then flushed to the tree as a new leaf node.
    pub head: SmallVec<[T; LEAF_CAPACITY]>,
    /// Height of the tree (0 for single leaf).
    ///
    /// The height determines how many levels of branch nodes exist
    /// between the root and the leaf nodes.
    pub height: usize,
    /// Total number of elements in the tree.
    ///
    /// This is the sum of elements in head, tree, and tail.
    pub len: usize,
}

/// Read-only methods that don't require Clone
impl<T> RRBTree<T> {
    /// Gets a reference to the element at the specified index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        if index < self.head.len() {
            return self.head.get(index);
        }

        let adjusted_index = index - self.head.len();
        let tree_size = self.len - self.head.len() - self.tail.len();

        if adjusted_index < tree_size {
            self.get_from_tree(adjusted_index)
        } else {
            let tail_index = adjusted_index - tree_size;
            self.tail.get(tail_index)
        }
    }

    fn get_from_tree(&self, index: usize) -> Option<&T> {
        let mut current_node = &self.root;
        let mut remaining_index = index;

        loop {
            match current_node.as_ref() {
                RRBNode::Leaf { elements } => {
                    return elements.get(remaining_index);
                },
                RRBNode::Branch { children, .. } => {
                    let (child_idx, sub_index) =
                        current_node.find_child_relaxed(remaining_index)?;

                    current_node = children.get(child_idx)?;
                    remaining_index = sub_index;
                },
            }
        }
    }

    /// Builds a tree by consuming its input without intermediate allocations.
    /// This is the primary path used to construct trees from any iterable sequence.
    pub fn from_elements<I: IntoIterator<Item = T>>(elements: I) -> Self {
        let mut iter = elements.into_iter();
        let mut leaves = Vec::new();
        let mut pending = SmallVec::<[T; LEAF_CAPACITY]>::new();
        let mut len = 0;

        loop {
            let chunk: SmallVec<[T; LEAF_CAPACITY]> = iter.by_ref().take(LEAF_CAPACITY).collect();
            if chunk.is_empty() {
                break;
            }
            len += chunk.len();
            if !pending.is_empty() {
                leaves.push(Arc::new(RRBNode::Leaf {
                    elements: std::mem::replace(&mut pending, chunk),
                }));
            } else {
                pending = chunk;
            }
        }

        if leaves.is_empty() {
            return Self {
                root: Arc::new(RRBNode::Leaf { elements: pending }),
                tail: SmallVec::new(),
                head: SmallVec::new(),
                height: 0,
                len,
            };
        }

        let tail = if pending.len() == LEAF_CAPACITY {
            leaves.push(Arc::new(RRBNode::Leaf { elements: pending }));
            SmallVec::new()
        } else {
            pending
        };
        let (root, height) = Self::build_tree_recursive(leaves);
        Self {
            root,
            tail,
            head: SmallVec::new(),
            height,
            len,
        }
    }

    fn build_tree_recursive(nodes: Vec<Arc<RRBNode<T>>>) -> (Arc<RRBNode<T>>, usize) {
        if nodes.len() == 1 {
            return (nodes.into_iter().next().expect("one node"), 0);
        }

        let mut iter = nodes.into_iter();
        let mut next_level = Vec::new();
        loop {
            let Some(first) = iter.next() else { break };
            let mut children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]> = SmallVec::new();
            children.push(first);
            for _ in 1..BRANCHING_FACTOR {
                let Some(child) = iter.next() else { break };
                children.push(child);
            }
            let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> = children
                .iter()
                .map(|child| child.calculate_size())
                .collect();
            next_level.push(Arc::new(RRBNode::Branch { children, sizes }));
        }
        let (root, height) = Self::build_tree_recursive(next_level);
        (root, height + 1)
    }
}

impl<T: Clone> RRBTree<T> {
    /// Consumes the tree and moves values out of uniquely owned nodes.
    /// Shared nodes are cloned only at the leaf boundary.
    pub fn into_vec(self) -> Vec<T> {
        fn drain_node<T: Clone>(node: Arc<RRBNode<T>>, out: &mut Vec<T>) {
            match Arc::try_unwrap(node) {
                Ok(RRBNode::Leaf { elements }) => out.extend(elements.into_vec()),
                Ok(RRBNode::Branch { children, .. }) => {
                    for child in children {
                        drain_node(child, out);
                    }
                },
                Err(node) => match node.as_ref() {
                    RRBNode::Leaf { elements } => out.extend(elements.iter().cloned()),
                    RRBNode::Branch { children, .. } => {
                        for child in children {
                            drain_node(Arc::clone(child), out);
                        }
                    },
                },
            }
        }

        let mut out = Vec::with_capacity(self.len);
        let head_len = self.head.len();
        let tail_len = self.tail.len();
        out.extend(self.head);
        let tree_size = self.len.saturating_sub(head_len + tail_len);
        if tree_size > 0 {
            drain_node(self.root, &mut out);
        }
        out.extend(self.tail);
        out
    }
}

/// Methods that require Clone for structural modifications
impl<T: Clone> RRBTree<T> {
    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.len {
            return self.clone();
        }

        if index < self.head.len() {
            let mut new_head = self.head.clone();
            new_head[index] = value;
            return Self {
                root: self.root.clone(),
                tail: self.tail.clone(),
                head: new_head,
                height: self.height,
                len: self.len,
            };
        }

        let adjusted_index = index - self.head.len();
        let tree_size = self.len - self.head.len() - self.tail.len();

        if adjusted_index < tree_size {
            let new_root = self.root.update(adjusted_index, value);
            Self {
                root: Arc::new(new_root),
                tail: self.tail.clone(),
                head: self.head.clone(),
                height: self.height,
                len: self.len,
            }
        } else {
            let tail_index = adjusted_index - tree_size;
            let mut new_tail = self.tail.clone();
            if tail_index < new_tail.len() {
                new_tail[tail_index] = value;
            }
            Self {
                root: self.root.clone(),
                tail: new_tail,
                head: self.head.clone(),
                height: self.height,
                len: self.len,
            }
        }
    }

    pub fn push_back(&self, value: T) -> Self {
        if self.tail.len() < LEAF_CAPACITY {
            let mut new_tail = self.tail.clone();
            new_tail.push(value);
            Self {
                root: self.root.clone(),
                tail: new_tail,
                head: self.head.clone(),
                height: self.height,
                len: self.len + 1,
            }
        } else {
            self.push_tail_to_tree().push_back(value)
        }
    }

    fn push_tail_to_tree(&self) -> Self {
        if self.tail.is_empty() {
            return self.clone();
        }

        let tail_leaf = Arc::new(RRBNode::Leaf {
            elements: self.tail.clone(),
        });

        if self.height == 0 {
            if self.root.calculate_size() == 0 {
                Self {
                    root: tail_leaf,
                    tail: SmallVec::new(),
                    head: self.head.clone(),
                    height: 0,
                    len: self.len,
                }
            } else {
                let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                    SmallVec::from_iter([self.root.calculate_size(), tail_leaf.calculate_size()]);
                let new_root = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([self.root.clone(), tail_leaf]),
                    sizes,
                });
                Self {
                    root: new_root,
                    tail: SmallVec::new(),
                    head: self.head.clone(),
                    height: 1,
                    len: self.len,
                }
            }
        } else {
            match RRBNode::push_back_leaf_recursive(&self.root, tail_leaf, self.height) {
                Ok(new_root) => Self {
                    root: new_root,
                    tail: SmallVec::new(),
                    head: self.head.clone(),
                    height: self.height,
                    len: self.len,
                },
                Err(new_sibling) => {
                    let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> = SmallVec::from_iter([
                        self.root.calculate_size(),
                        new_sibling.calculate_size(),
                    ]);
                    let new_root = Arc::new(RRBNode::Branch {
                        children: SmallVec::from_iter([self.root.clone(), new_sibling]),
                        sizes,
                    });
                    Self {
                        root: new_root,
                        tail: SmallVec::new(),
                        head: self.head.clone(),
                        height: self.height + 1,
                        len: self.len,
                    }
                },
            }
        }
    }

    pub fn push_front(&self, value: T) -> Self {
        if self.head.len() < LEAF_CAPACITY {
            let mut new_head = SmallVec::with_capacity(self.head.len() + 1);
            new_head.push(value);
            new_head.extend(self.head.iter().cloned());
            Self {
                root: self.root.clone(),
                tail: self.tail.clone(),
                head: new_head,
                height: self.height,
                len: self.len + 1,
            }
        } else {
            self.push_head_to_tree().push_front(value)
        }
    }

    fn push_head_to_tree(&self) -> Self {
        if self.head.is_empty() {
            return self.clone();
        }

        let head_leaf = Arc::new(RRBNode::Leaf {
            elements: self.head.clone(),
        });

        if self.height == 0 {
            if self.root.calculate_size() == 0 {
                Self {
                    root: head_leaf,
                    tail: self.tail.clone(),
                    head: SmallVec::new(),
                    height: 0,
                    len: self.len,
                }
            } else {
                let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                    SmallVec::from_iter([head_leaf.calculate_size(), self.root.calculate_size()]);
                let new_root = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([head_leaf, self.root.clone()]),
                    sizes,
                });
                Self {
                    root: new_root,
                    tail: self.tail.clone(),
                    head: SmallVec::new(),
                    height: 1,
                    len: self.len,
                }
            }
        } else {
            match RRBNode::push_front_leaf_recursive(&self.root, head_leaf, self.height) {
                Ok(new_root) => Self {
                    root: new_root,
                    tail: self.tail.clone(),
                    head: SmallVec::new(),
                    height: self.height,
                    len: self.len,
                },
                Err(new_sibling) => {
                    let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> = SmallVec::from_iter([
                        new_sibling.calculate_size(),
                        self.root.calculate_size(),
                    ]);
                    let new_root = Arc::new(RRBNode::Branch {
                        children: SmallVec::from_iter([new_sibling, self.root.clone()]),
                        sizes,
                    });
                    Self {
                        root: new_root,
                        tail: self.tail.clone(),
                        head: SmallVec::new(),
                        height: self.height + 1,
                        len: self.len,
                    }
                },
            }
        }
    }

    pub fn concat(&self, other: &Self) -> Self {
        if self.len == 0 {
            return other.clone();
        }
        if other.len == 0 {
            return self.clone();
        }

        let mut left_for_merge = self.clone();
        let mut right_for_merge = other.clone();

        if !left_for_merge.tail.is_empty() {
            left_for_merge = left_for_merge.push_tail_to_tree();
        }

        if !right_for_merge.head.is_empty() {
            right_for_merge = right_for_merge.push_head_to_tree();
        }

        if left_for_merge.height == right_for_merge.height {
            Self::concat_flushed_same_height(&left_for_merge, &right_for_merge)
        } else if left_for_merge.height < right_for_merge.height {
            let elevated_left = Self::elevate_tree(&left_for_merge, right_for_merge.height);
            Self::concat_flushed_same_height(&elevated_left, &right_for_merge)
        } else {
            let elevated_right = Self::elevate_tree(&right_for_merge, left_for_merge.height);
            Self::concat_flushed_same_height(&left_for_merge, &elevated_right)
        }
    }

    fn concat_flushed_same_height(left: &Self, right: &Self) -> Self {
        let mut merged_nodes = Self::concat_nodes(&left.root, &right.root, left.height);
        let (root, height) = if merged_nodes.len() == 1 {
            let root = match merged_nodes.pop() {
                Some(root) => root,
                None => unreachable!("concatenating non-empty trees produces a root"),
            };
            (root, left.height)
        } else {
            let (root, additional_height) = Self::build_tree_recursive(merged_nodes);
            (root, left.height + additional_height)
        };

        Self {
            root,
            tail: right.tail.clone(),
            head: left.head.clone(),
            height,
            len: left.len + right.len,
        }
    }

    fn elevate_tree(tree: &Self, target_height: usize) -> Self {
        let mut current_root = tree.root.clone();
        let mut current_height = tree.height;

        while current_height < target_height {
            let new_root = RRBNode::Branch {
                children: SmallVec::from_iter([current_root.clone()]),
                sizes: SmallVec::from_iter([current_root.calculate_size()]),
            };
            current_root = Arc::new(new_root);
            current_height += 1;
        }

        Self {
            root: current_root,
            tail: tree.tail.clone(),
            head: tree.head.clone(),
            height: current_height,
            len: tree.len,
        }
    }

    fn pack_children(children: Vec<Arc<RRBNode<T>>>) -> Vec<Arc<RRBNode<T>>> {
        children
            .chunks(BRANCHING_FACTOR)
            .map(|chunk| Arc::new(RRBNode::make_relaxed(chunk.to_vec())))
            .collect()
    }

    fn concat_nodes(
        left: &Arc<RRBNode<T>>, right: &Arc<RRBNode<T>>, height: usize,
    ) -> Vec<Arc<RRBNode<T>>> {
        match (left.as_ref(), right.as_ref()) {
            (
                RRBNode::Leaf {
                    elements: left_elems,
                },
                RRBNode::Leaf {
                    elements: right_elems,
                },
            ) => {
                let mut combined = left_elems.clone();
                combined.extend(right_elems.iter().cloned());

                if combined.len() <= LEAF_CAPACITY {
                    vec![Arc::new(RRBNode::Leaf { elements: combined })]
                } else {
                    let left_part =
                        SmallVec::from_iter(combined.iter().take(LEAF_CAPACITY).cloned());
                    let right_part =
                        SmallVec::from_iter(combined.iter().skip(LEAF_CAPACITY).cloned());

                    vec![
                        Arc::new(RRBNode::Leaf {
                            elements: left_part,
                        }),
                        Arc::new(RRBNode::Leaf {
                            elements: right_part,
                        }),
                    ]
                }
            },
            (
                RRBNode::Branch {
                    children: left_children,
                    ..
                },
                RRBNode::Branch {
                    children: right_children,
                    ..
                },
            ) => {
                let mut new_children = Vec::new();

                for child in left_children
                    .iter()
                    .take(left_children.len().saturating_sub(1))
                {
                    new_children.push(child.clone());
                }

                if let (Some(left_last), Some(right_first)) =
                    (left_children.last(), right_children.first())
                {
                    let next_height = height.saturating_sub(1);
                    new_children.extend(Self::concat_nodes(left_last, right_first, next_height));
                }

                new_children.extend(right_children.iter().skip(1).cloned());
                Self::pack_children(new_children)
            },
            (RRBNode::Leaf { .. }, RRBNode::Branch { .. })
            | (RRBNode::Branch { .. }, RRBNode::Leaf { .. }) => {
                unreachable!("nodes at equal tree height must both be leaves or both branches")
            },
        }
    }

    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.len == 0 {
            return None;
        }

        if !self.tail.is_empty() {
            let mut new_tail = self.tail.clone();
            let popped = new_tail.pop()?;
            Some((
                Self {
                    root: self.root.clone(),
                    tail: new_tail,
                    head: self.head.clone(),
                    height: self.height,
                    len: self.len - 1,
                },
                popped,
            ))
        } else {
            let tree_size = self.len - self.head.len() - self.tail.len();
            if tree_size == 0 {
                let mut new_head = self.head.clone();
                let popped = new_head.pop()?;
                return Some((
                    Self {
                        root: self.root.clone(),
                        tail: self.tail.clone(),
                        head: new_head,
                        height: self.height,
                        len: self.len - 1,
                    },
                    popped,
                ));
            }
            self.pop_from_tree()
        }
    }

    fn pop_from_tree(&self) -> Option<(Self, T)> {
        let tree_size = self.len - self.head.len() - self.tail.len();
        if tree_size > 0
            && let Some((new_root, popped)) = self.root.pop_back()
        {
            let new_height = if tree_size == 1 { 0 } else { self.height };
            return Some((
                Self {
                    root: Arc::new(new_root),
                    tail: self.tail.clone(),
                    head: self.head.clone(),
                    height: new_height,
                    len: self.len - 1,
                },
                popped,
            ));
        }
        None
    }

    pub fn pop_front(&self) -> Option<(Self, T)> {
        if self.len == 0 {
            return None;
        }

        if !self.head.is_empty() {
            let mut new_head = self.head.clone();
            let popped = new_head.remove(0);
            Some((
                Self {
                    root: self.root.clone(),
                    tail: self.tail.clone(),
                    head: new_head,
                    height: self.height,
                    len: self.len - 1,
                },
                popped,
            ))
        } else {
            self.pop_front_from_tree()
        }
    }

    fn pop_front_from_tree(&self) -> Option<(Self, T)> {
        let tree_size = self.len - self.head.len() - self.tail.len();
        if tree_size > 0
            && let Some((new_root, popped_element)) = self.root.pop_front()
        {
            let new_height = if tree_size == 1 { 0 } else { self.height };
            return Some((
                Self {
                    root: Arc::new(new_root),
                    tail: self.tail.clone(),
                    head: self.head.clone(),
                    height: new_height,
                    len: self.len - 1,
                },
                popped_element,
            ));
        }

        if !self.tail.is_empty() {
            let popped = self.tail[0].clone();
            let new_head = self.tail[1..].iter().cloned().collect();

            Some((
                Self {
                    root: Arc::new(RRBNode::Leaf {
                        elements: SmallVec::new(),
                    }),
                    tail: SmallVec::new(),
                    head: new_head,
                    height: 0,
                    len: self.len - 1,
                },
                popped,
            ))
        } else {
            None
        }
    }

    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index == 0 {
            return (Self::empty(), self.clone());
        }
        if index >= self.len {
            return (self.clone(), Self::empty());
        }

        if index <= self.head.len() {
            let (left_head, right_head) = self.split_head_at(index);
            return (
                Self::from_head(left_head),
                Self::from_head_and_tree_and_tail(
                    right_head,
                    self.root.clone(),
                    self.tail.clone(),
                    self.height,
                ),
            );
        }

        let tree_start = self.head.len();
        let tree_size = self.len - self.head.len() - self.tail.len();

        if index >= tree_start + tree_size {
            let tail_index = index - tree_start - tree_size;
            let (left_tail, right_tail) = self.split_tail_at(tail_index);
            return (
                Self::from_head_and_tree_and_tail(
                    self.head.clone(),
                    self.root.clone(),
                    left_tail,
                    self.height,
                ),
                Self::from_tail(right_tail),
            );
        }

        let tree_index = index - tree_start;
        let (left_root, right_root) = self.split_tree_at(tree_index);

        (
            Self::from_head_and_root(self.head.clone(), left_root),
            Self::from_root_and_tail(right_root, self.tail.clone()),
        )
    }

    fn split_tree_at(&self, index: usize) -> (Arc<RRBNode<T>>, Arc<RRBNode<T>>) {
        let path = self.find_path_to_index(index);
        self.split_along_path(&path, index, &self.root, self.height)
    }

    fn split_along_path(
        &self, path: &[usize], target_index: usize, node: &Arc<RRBNode<T>>, current_height: usize,
    ) -> (Arc<RRBNode<T>>, Arc<RRBNode<T>>) {
        match node.as_ref() {
            RRBNode::Leaf { .. } => self.split_leaf_node(node, target_index),
            RRBNode::Branch { children, sizes } => {
                if path.is_empty() {
                    if let Some(first_child) = children.first() {
                        let next_height = current_height.saturating_sub(1);
                        return self.split_along_path(&[], target_index, first_child, next_height);
                    } else {
                        let empty_leaf = Arc::new(RRBNode::Leaf {
                            elements: SmallVec::new(),
                        });
                        return (empty_leaf.clone(), empty_leaf);
                    }
                }

                let child_index = path[0];
                let remaining_path = &path[1..];

                if let Some(child) = children.get(child_index) {
                    let adjusted_index =
                        self.calculate_adjusted_index(target_index, child_index, sizes);

                    let next_height = current_height.saturating_sub(1);
                    let (left_child, right_child) =
                        self.split_along_path(remaining_path, adjusted_index, child, next_height);

                    let left_branch = self.create_left_branch(children, child_index, left_child);
                    let right_branch = self.create_right_branch(children, child_index, right_child);

                    (Arc::new(left_branch), Arc::new(right_branch))
                } else {
                    let empty_leaf = Arc::new(RRBNode::Leaf {
                        elements: SmallVec::new(),
                    });
                    (empty_leaf.clone(), empty_leaf)
                }
            },
        }
    }

    fn split_leaf_node(
        &self, node: &Arc<RRBNode<T>>, index: usize,
    ) -> (Arc<RRBNode<T>>, Arc<RRBNode<T>>) {
        match node.as_ref() {
            RRBNode::Leaf { elements } => {
                let split_idx = index.min(elements.len());
                let left_elements = elements.iter().take(split_idx).cloned().collect();
                let right_elements = elements.iter().skip(split_idx).cloned().collect();

                (
                    Arc::new(RRBNode::Leaf {
                        elements: left_elements,
                    }),
                    Arc::new(RRBNode::Leaf {
                        elements: right_elements,
                    }),
                )
            },
            _ => unreachable!("Expected leaf node"),
        }
    }

    fn create_left_branch(
        &self, original_children: &SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        split_index: usize, new_child: Arc<RRBNode<T>>,
    ) -> RRBNode<T> {
        let mut left_children = Vec::new();

        for i in 0..split_index {
            left_children.push(original_children[i].clone());
        }

        if new_child.calculate_size() > 0 {
            left_children.push(new_child);
        }

        if left_children.is_empty() {
            RRBNode::Leaf {
                elements: SmallVec::new(),
            }
        } else {
            RRBNode::make_relaxed(left_children)
        }
    }

    fn create_right_branch(
        &self, original_children: &SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        split_index: usize, new_child: Arc<RRBNode<T>>,
    ) -> RRBNode<T> {
        let mut right_children = Vec::new();

        if new_child.calculate_size() > 0 {
            right_children.push(new_child);
        }

        for i in (split_index + 1)..original_children.len() {
            right_children.push(original_children[i].clone());
        }

        if right_children.is_empty() {
            RRBNode::Leaf {
                elements: SmallVec::new(),
            }
        } else {
            RRBNode::make_relaxed(right_children)
        }
    }

    fn calculate_adjusted_index(
        &self, target_index: usize, child_index: usize,
        sizes: &SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>,
    ) -> usize {
        let mut cumulative = 0;
        for i in 0..child_index {
            cumulative += sizes.get(i).unwrap_or(&0);
        }
        target_index.saturating_sub(cumulative)
    }

    fn find_path_to_index(&self, index: usize) -> Vec<usize> {
        let mut path = Vec::new();
        let mut current_node = &self.root;
        let mut remaining_index = index;
        let mut current_height = self.height;

        while current_height > 0 {
            match current_node.as_ref() {
                RRBNode::Branch { children, .. } => {
                    let (child_idx, sub_index) = current_node
                        .find_child_relaxed(remaining_index)
                        .unwrap_or((0, 0));

                    path.push(child_idx);
                    remaining_index = sub_index;

                    if let Some(child) = children.get(child_idx) {
                        current_node = child;
                    } else {
                        break;
                    }
                    current_height = current_height.saturating_sub(1);
                },
                RRBNode::Leaf { .. } => break,
            }
        }
        path
    }

    fn empty() -> Self {
        Self {
            root: Arc::new(RRBNode::Leaf {
                elements: SmallVec::new(),
            }),
            tail: SmallVec::new(),
            head: SmallVec::new(),
            height: 0,
            len: 0,
        }
    }

    fn from_head(head: SmallVec<[T; LEAF_CAPACITY]>) -> Self {
        Self {
            root: Arc::new(RRBNode::Leaf {
                elements: SmallVec::new(),
            }),
            tail: SmallVec::new(),
            head: head.clone(),
            height: 0,
            len: head.len(),
        }
    }

    fn from_tail(tail: SmallVec<[T; LEAF_CAPACITY]>) -> Self {
        Self {
            root: Arc::new(RRBNode::Leaf {
                elements: SmallVec::new(),
            }),
            tail: tail.clone(),
            head: SmallVec::new(),
            height: 0,
            len: tail.len(),
        }
    }

    fn from_head_and_tree_and_tail(
        head: SmallVec<[T; LEAF_CAPACITY]>, root: Arc<RRBNode<T>>,
        tail: SmallVec<[T; LEAF_CAPACITY]>, height: usize,
    ) -> Self {
        let tree_size = root.calculate_size();
        Self {
            root,
            tail: tail.clone(),
            head: head.clone(),
            height,
            len: head.len() + tree_size + tail.len(),
        }
    }

    fn from_head_and_root(head: SmallVec<[T; LEAF_CAPACITY]>, root: Arc<RRBNode<T>>) -> Self {
        let tree_size = root.calculate_size();
        let height = Self::calculate_height(&root);
        Self {
            root,
            tail: SmallVec::new(),
            head: head.clone(),
            height,
            len: head.len() + tree_size,
        }
    }

    fn from_root_and_tail(root: Arc<RRBNode<T>>, tail: SmallVec<[T; LEAF_CAPACITY]>) -> Self {
        let tree_size = root.calculate_size();
        let height = Self::calculate_height(&root);
        Self {
            root,
            tail: tail.clone(),
            head: SmallVec::new(),
            height,
            len: tree_size + tail.len(),
        }
    }

    fn split_head_at(
        &self, index: usize,
    ) -> (SmallVec<[T; LEAF_CAPACITY]>, SmallVec<[T; LEAF_CAPACITY]>) {
        let left = SmallVec::from_iter(self.head.iter().take(index).cloned());
        let right = SmallVec::from_iter(self.head.iter().skip(index).cloned());
        (left, right)
    }

    fn split_tail_at(
        &self, index: usize,
    ) -> (SmallVec<[T; LEAF_CAPACITY]>, SmallVec<[T; LEAF_CAPACITY]>) {
        let left = SmallVec::from_iter(self.tail.iter().take(index).cloned());
        let right = SmallVec::from_iter(self.tail.iter().skip(index).cloned());
        (left, right)
    }

    fn calculate_height(node: &Arc<RRBNode<T>>) -> usize {
        match node.as_ref() {
            RRBNode::Leaf { .. } => 0,
            RRBNode::Branch { children, .. } => {
                if let Some(first_child) = children.first() {
                    1 + Self::calculate_height(first_child)
                } else {
                    0
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::RRBTree;
    use crate::pvec::node::{BRANCHING_FACTOR, RRBNode};
    use std::sync::Arc;

    fn assert_branch_width<T>(node: &Arc<RRBNode<T>>) {
        if let RRBNode::Branch { children, .. } = node.as_ref() {
            assert!(children.len() <= BRANCHING_FACTOR);
            for child in children {
                assert_branch_width(child);
            }
        }
    }

    #[test]
    fn concat_keeps_every_branch_within_the_branching_factor() {
        let chunk: Vec<_> = (0..2048).collect();
        let mut tree = RRBTree::from_elements(chunk.clone());
        let mut expected = chunk.clone();

        for _ in 1..4 {
            tree = tree.concat(&RRBTree::from_elements(chunk.clone()));
            expected.extend_from_slice(&chunk);
            assert_branch_width(&tree.root);
            assert_eq!(tree.clone().into_vec(), expected);
        }
    }

    #[test]
    fn bounded_concat_preserves_order_and_access() {
        let left = RRBTree::from_elements(0..2048);
        let right = RRBTree::from_elements(2048..4096);
        let merged = left.concat(&right);

        assert_branch_width(&merged.root);
        assert_eq!(merged.len, 4096);
        assert_eq!(merged.get(0), Some(&0));
        assert_eq!(merged.get(2047), Some(&2047));
        assert_eq!(merged.get(2048), Some(&2048));
        assert_eq!(merged.get(4095), Some(&4095));
        assert_eq!(merged.clone().into_vec(), (0..4096).collect::<Vec<_>>());
        assert_eq!(left.into_vec(), (0..2048).collect::<Vec<_>>());
    }

    #[test]
    fn pop_front_from_tail_preserves_order() {
        let mut tree = RRBTree::from_elements(0..67);
        for i in 0..64 {
            let (next, popped) = tree.pop_front().unwrap();
            assert_eq!(popped, i);
            tree = next;
        }
        let (tree2, popped) = tree.pop_front().unwrap();
        assert_eq!(popped, 64);
        assert_eq!(tree2.get(0), Some(&65));
        assert_eq!(tree2.get(1), Some(&66));
        let (tree3, popped) = tree2.pop_front().unwrap();
        assert_eq!(popped, 65);
        let (tree4, popped) = tree3.pop_front().unwrap();
        assert_eq!(popped, 66);
        assert!(tree4.pop_front().is_none());
    }

    #[test]
    fn pop_back_from_tree_single_pass() {
        let mut tree = RRBTree::from_elements(0..128);
        assert!(tree.tail.is_empty());
        for expected in (0..128).rev() {
            let (next, popped) = tree.pop_back().expect("non-empty");
            assert_eq!(popped, expected);
            assert_eq!(next.len, expected as usize);
            tree = next;
        }
        assert_eq!(tree.len, 0);
        assert!(tree.pop_back().is_none());
    }
}
