//! Iterators for persistent vectors.
//!
//! This module provides iterator types for [`PersistentVector`], enabling
//! idiomatic Rust iteration patterns over persistent vector elements.
//!
//! # Iterator Types
//!
//! - [`PersistentVectorIter`]: Borrows the vector and yields references (`&T`)
//! - [`PersistentVectorIntoIter`]: Consumes the vector and yields owned values (`T`)
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::PersistentVector;
//!
//! let vec = PersistentVector::from_slice(&[1, 2, 3]);
//!
//! // Iterate by reference
//! for item in vec.iter() {
//!     println!("{}", item);
//! }
//!
//! // Iterate by value (consumes the vector)
//! let sum: i32 = vec.into_iter().sum();
//! assert_eq!(sum, 6);
//! ```

use smallvec::SmallVec;
use std::sync::Arc;

use super::core::{ADAPTIVE_INLINE_SIZE, PersistentVector, VectorImpl};
use super::node::{LEAF_CAPACITY, RRBNode, SMALL_BRANCH_SIZE};
use super::tree::RRBTree;

/// Stack entry for tree traversal.
type StackEntry<'a, T> = (&'a Arc<RRBNode<T>>, usize);

/// An iterator over references to elements in a persistent vector.
///
/// This iterator uses an optimized O(n) traversal strategy instead of
/// calling `get()` for each element (which would be O(n log n)).
///
/// [`iter`]: super::core::PersistentVector::iter
///
pub struct PersistentVectorIter<'a, T> {
    /// Current traversal state
    state: IterState<'a, T>,
    /// Total remaining elements (front to back)
    remaining: usize,
}

/// Internal state for efficient iteration
enum IterState<'a, T> {
    /// Iterating over inline storage
    Inline {
        slice: &'a [T],
        front: usize,
        back: usize,
    },
    /// Iterating over tree storage (boxed to reduce enum size)
    Tree(Box<TreeIterState<'a, T>>),
    /// Iteration complete
    Done,
}

/// State for tree-based iteration
struct TreeIterState<'a, T> {
    tree: &'a RRBTree<T>,
    /// Current phase of iteration
    phase: TreePhase,
    /// Stack for tree traversal (node, child_index)
    stack: SmallVec<[StackEntry<'a, T>; SMALL_BRANCH_SIZE]>,
    /// Current leaf slice being iterated
    current_leaf: Option<&'a [T]>,
    /// Index within current leaf
    leaf_front: usize,
    leaf_back: usize,
    /// Back iteration position tracking
    back_phase: TreePhase,
    back_stack: SmallVec<[StackEntry<'a, T>; SMALL_BRANCH_SIZE]>,
    back_leaf: Option<&'a [T]>,
    back_leaf_front: usize,
    back_leaf_back: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TreePhase {
    Head,
    Tree,
    Tail,
    Done,
}

impl<'a, T> PersistentVectorIter<'a, T> {
    /// Creates a new iterator over the vector.
    pub(crate) fn new(vector: &'a PersistentVector<T>) -> Self {
        let len = vector.len();
        if len == 0 {
            return Self {
                state: IterState::Done,
                remaining: 0,
            };
        }

        let state = match &vector.inner {
            VectorImpl::Inline { elements } => IterState::Inline {
                slice: elements.as_slice(),
                front: 0,
                back: elements.len(),
            },
            VectorImpl::Tree { tree } => {
                let mut tree_state = TreeIterState {
                    tree: tree.as_ref(),
                    phase: if !tree.head.is_empty() {
                        TreePhase::Head
                    } else {
                        TreePhase::Tree
                    },
                    stack: SmallVec::new(),
                    current_leaf: None,
                    leaf_front: 0,
                    leaf_back: 0,
                    back_phase: if !tree.tail.is_empty() {
                        TreePhase::Tail
                    } else {
                        TreePhase::Tree
                    },
                    back_stack: SmallVec::new(),
                    back_leaf: None,
                    back_leaf_front: 0,
                    back_leaf_back: 0,
                };

                // Initialize front: Head → Tree → Tail order
                match tree_state.phase {
                    TreePhase::Head => {
                        tree_state.current_leaf = Some(tree.head.as_slice());
                        tree_state.leaf_back = tree.head.len();
                    },
                    TreePhase::Tree => {
                        // If head is empty, start from tree
                        tree_state.init_tree_front();
                    },
                    _ => {},
                }

                // Initialize back: Tail → Tree → Head order
                match tree_state.back_phase {
                    TreePhase::Tail => {
                        tree_state.back_leaf = Some(tree.tail.as_slice());
                        tree_state.back_leaf_back = tree.tail.len();
                    },
                    TreePhase::Tree => {
                        // If tail is empty, start from tree
                        tree_state.init_tree_back();
                    },
                    _ => {},
                }

                IterState::Tree(Box::new(tree_state))
            },
        };

        Self {
            state,
            remaining: len,
        }
    }
}

impl<'a, T> Iterator for PersistentVectorIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        let result = match &mut self.state {
            IterState::Done => return None,
            IterState::Inline { slice, front, back } => {
                if *front < *back {
                    let item = &slice[*front];
                    *front += 1;
                    Some(item)
                } else {
                    None
                }
            },
            IterState::Tree(ts) => ts.next_front(),
        };

        if result.is_some() {
            self.remaining -= 1;
        }
        result
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> ExactSizeIterator for PersistentVectorIter<'_, T> {}

impl<'a, T> DoubleEndedIterator for PersistentVectorIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        let result = match &mut self.state {
            IterState::Done => return None,
            IterState::Inline { slice, front, back } => {
                if *front < *back {
                    *back -= 1;
                    Some(&slice[*back])
                } else {
                    None
                }
            },
            IterState::Tree(ts) => ts.next_back(),
        };

        if result.is_some() {
            self.remaining -= 1;
        }
        result
    }
}

impl<'a, T> TreeIterState<'a, T> {
    fn next_front(&mut self) -> Option<&'a T> {
        loop {
            // Try current leaf first
            if let Some(leaf) = self
                .current_leaf
                .filter(|_| self.leaf_front < self.leaf_back)
            {
                let item = &leaf[self.leaf_front];
                self.leaf_front += 1;
                return Some(item);
            }

            // Need to move to next segment
            match self.phase {
                TreePhase::Head => {
                    self.phase = TreePhase::Tree;
                    self.current_leaf = None;
                    self.leaf_front = 0;
                    self.leaf_back = 0;
                    // Initialize tree traversal only if not already done
                    if self.stack.is_empty() {
                        self.init_tree_front();
                    }
                },
                TreePhase::Tree => {
                    // Try to get next leaf from tree
                    if !self.advance_tree_front() {
                        self.phase = TreePhase::Tail;
                        if !self.tree.tail.is_empty() {
                            self.current_leaf = Some(self.tree.tail.as_slice());
                            self.leaf_front = 0;
                            self.leaf_back = self.tree.tail.len();
                        }
                    }
                },
                TreePhase::Tail => {
                    self.phase = TreePhase::Done;
                    return None;
                },
                TreePhase::Done => return None,
            }
        }
    }

    fn next_back(&mut self) -> Option<&'a T> {
        loop {
            // Try current back leaf first
            if let Some(leaf) = self
                .back_leaf
                .filter(|_| self.back_leaf_front < self.back_leaf_back)
            {
                self.back_leaf_back -= 1;
                return Some(&leaf[self.back_leaf_back]);
            }

            // Need to move to previous segment
            match self.back_phase {
                TreePhase::Tail => {
                    self.back_phase = TreePhase::Tree;
                    self.back_leaf = None;
                    self.back_leaf_front = 0;
                    self.back_leaf_back = 0;
                    // Initialize back tree traversal only if not already done
                    if self.back_stack.is_empty() {
                        self.init_tree_back();
                    }
                },
                TreePhase::Tree => {
                    // Try to get previous leaf from tree
                    if !self.advance_tree_back() {
                        self.back_phase = TreePhase::Head;
                        if !self.tree.head.is_empty() {
                            self.back_leaf = Some(self.tree.head.as_slice());
                            self.back_leaf_front = 0;
                            self.back_leaf_back = self.tree.head.len();
                        }
                    }
                },
                TreePhase::Head => {
                    self.back_phase = TreePhase::Done;
                    return None;
                },
                TreePhase::Done => return None,
            }
        }
    }

    fn init_tree_front(&mut self) {
        self.stack.clear();
        let tree_size = self.tree.len - self.tree.head.len() - self.tree.tail.len();
        if tree_size == 0 {
            return;
        }

        // Descend to leftmost leaf
        let mut node = &self.tree.root;
        loop {
            match node.as_ref() {
                RRBNode::Leaf { elements } => {
                    self.current_leaf = Some(elements.as_slice());
                    self.leaf_front = 0;
                    self.leaf_back = elements.len();
                    break;
                },
                RRBNode::Branch { children, .. } => {
                    if children.is_empty() {
                        break;
                    }
                    self.stack.push((node, 0));
                    node = &children[0];
                },
            }
        }
    }

    fn advance_tree_front(&mut self) -> bool {
        while let Some((node, idx)) = self.stack.pop() {
            if let Some(found) = self.try_advance_front(node, idx) {
                return found;
            }
        }
        self.current_leaf = None;
        false
    }

    fn try_advance_front(&mut self, node: &'a Arc<RRBNode<T>>, idx: usize) -> Option<bool> {
        let RRBNode::Branch { children, .. } = node.as_ref() else {
            return None;
        };
        let next_idx = idx + 1;
        if next_idx >= children.len() {
            return None;
        }
        self.stack.push((node, next_idx));
        self.descend_to_leftmost(&children[next_idx]);
        Some(self.current_leaf.is_some())
    }

    fn descend_to_leftmost(&mut self, start: &'a Arc<RRBNode<T>>) {
        let mut current = start;
        loop {
            match current.as_ref() {
                RRBNode::Leaf { elements } => {
                    self.current_leaf = Some(elements.as_slice());
                    self.leaf_front = 0;
                    self.leaf_back = elements.len();
                    return;
                },
                RRBNode::Branch { children, .. } if !children.is_empty() => {
                    self.stack.push((current, 0));
                    current = &children[0];
                },
                _ => return,
            }
        }
    }

    fn init_tree_back(&mut self) {
        self.back_stack.clear();
        let tree_size = self.tree.len - self.tree.head.len() - self.tree.tail.len();
        if tree_size == 0 {
            return;
        }

        // Descend to rightmost leaf
        let mut node = &self.tree.root;
        loop {
            match node.as_ref() {
                RRBNode::Leaf { elements } => {
                    self.back_leaf = Some(elements.as_slice());
                    self.back_leaf_front = 0;
                    self.back_leaf_back = elements.len();
                    break;
                },
                RRBNode::Branch { children, .. } => {
                    if children.is_empty() {
                        break;
                    }
                    let last_idx = children.len() - 1;
                    self.back_stack.push((node, last_idx));
                    node = &children[last_idx];
                },
            }
        }
    }

    fn advance_tree_back(&mut self) -> bool {
        while let Some((node, idx)) = self.back_stack.pop() {
            if let Some(found) = self.try_advance_back(node, idx) {
                return found;
            }
        }
        self.back_leaf = None;
        false
    }

    fn try_advance_back(&mut self, node: &'a Arc<RRBNode<T>>, idx: usize) -> Option<bool> {
        let RRBNode::Branch { children, .. } = node.as_ref() else {
            return None;
        };
        if idx == 0 {
            return None;
        }
        let prev_idx = idx - 1;
        self.back_stack.push((node, prev_idx));
        self.descend_to_rightmost(&children[prev_idx]);
        Some(self.back_leaf.is_some())
    }

    fn descend_to_rightmost(&mut self, start: &'a Arc<RRBNode<T>>) {
        let mut current = start;
        loop {
            match current.as_ref() {
                RRBNode::Leaf { elements } => {
                    self.back_leaf = Some(elements.as_slice());
                    self.back_leaf_front = 0;
                    self.back_leaf_back = elements.len();
                    return;
                },
                RRBNode::Branch { children, .. } if !children.is_empty() => {
                    let last = children.len() - 1;
                    self.back_stack.push((current, last));
                    current = &children[last];
                },
                _ => return,
            }
        }
    }
}

/// An iterator that yields owned elements from a persistent vector.
///
/// This iterator consumes the vector and yields owned values lazily
/// without eagerly materializing the entire vector as a `Vec<T>`.
pub struct PersistentVectorIntoIter<T> {
    state: IntoIterState<T>,
    remaining: usize,
}

enum IntoIterState<T> {
    Inline(smallvec::IntoIter<[T; ADAPTIVE_INLINE_SIZE]>),
    Tree(Box<TreeIntoIterState<T>>),
    Done,
}

struct TreeIntoIterState<T> {
    tree: Arc<RRBTree<T>>,
    front_index: usize,
    front_leaf: SmallVec<[T; LEAF_CAPACITY]>,
    front_pos: usize,
    back_index: usize,
    back_leaf: SmallVec<[T; LEAF_CAPACITY]>,
}

impl<T: Clone> PersistentVectorIntoIter<T> {
    pub(crate) fn new(vector: PersistentVector<T>) -> Self {
        let remaining = vector.len();
        if remaining == 0 {
            return Self {
                state: IntoIterState::Done,
                remaining: 0,
            };
        }

        let state = match vector.inner {
            VectorImpl::Inline { elements } => IntoIterState::Inline(elements.into_iter()),
            VectorImpl::Tree { tree } => IntoIterState::Tree(Box::new(TreeIntoIterState {
                front_index: 0,
                front_leaf: SmallVec::new(),
                front_pos: 0,
                back_index: tree.len,
                back_leaf: SmallVec::new(),
                tree,
            })),
        };

        Self { state, remaining }
    }
}

impl<T: Clone> Iterator for PersistentVectorIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        match &mut self.state {
            IntoIterState::Done => None,
            IntoIterState::Inline(iter) => {
                let item = iter.next();
                if item.is_some() {
                    self.remaining -= 1;
                }
                item
            },
            IntoIterState::Tree(ts) => {
                if ts.front_pos < ts.front_leaf.len() {
                    let item = ts.front_leaf[ts.front_pos].clone();
                    ts.front_pos += 1;
                    ts.front_index += 1;
                    self.remaining -= 1;
                    return Some(item);
                }

                ts.front_leaf.clear();
                ts.front_pos = 0;
                let (slice, offset) = ts.tree.get_leaf_slice(ts.front_index)?;
                ts.front_leaf.extend(slice[offset..].iter().cloned());
                if ts.front_leaf.is_empty() {
                    return None;
                }
                let item = ts.front_leaf[0].clone();
                ts.front_pos = 1;
                ts.front_index += 1;
                self.remaining -= 1;
                Some(item)
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T: Clone> ExactSizeIterator for PersistentVectorIntoIter<T> {}

impl<T: Clone> DoubleEndedIterator for PersistentVectorIntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        match &mut self.state {
            IntoIterState::Done => None,
            IntoIterState::Inline(iter) => {
                let item = iter.next_back();
                if item.is_some() {
                    self.remaining -= 1;
                }
                item
            },
            IntoIterState::Tree(ts) => {
                if let Some(item) = ts.back_leaf.pop() {
                    ts.back_index -= 1;
                    self.remaining -= 1;
                    return Some(item);
                }

                if ts.back_index == 0 {
                    return None;
                }

                let (slice, offset) = ts.tree.get_leaf_slice(ts.back_index - 1)?;
                ts.back_leaf.extend(slice[..=offset].iter().cloned());
                let item = ts.back_leaf.pop()?;
                ts.back_index -= 1;
                self.remaining -= 1;
                Some(item)
            },
        }
    }
}
