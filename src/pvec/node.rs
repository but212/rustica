//! Internal RRB tree node implementation.
//!
//! This module contains the core node structure for the RRB (Relaxed Radix Balanced) tree
//! that underlies the persistent vector implementation.

use smallvec::SmallVec;
use std::sync::Arc;

/// Maximum number of children per branch node.
pub const BRANCHING_FACTOR: usize = 32;
/// Maximum number of elements per leaf node.
pub const LEAF_CAPACITY: usize = 64;
/// Typical branch size for most nodes (optimization).
pub const SMALL_BRANCH_SIZE: usize = 8;
/// Corresponding size table for small branches.
pub const SMALL_SIZE_TABLE_SIZE: usize = 8;

/// A node in the RRB tree structure.
///
/// RRB nodes can be either branch nodes (containing child nodes) or leaf nodes
/// (containing actual data elements). Branch nodes may have a size table for
/// relaxed balancing when the tree becomes irregular.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RRBNode<T> {
    /// A branch node containing child nodes.
    Branch {
        /// Child nodes of this branch.
        children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        /// Optional size table for relaxed balancing. Present when the tree is irregular.
        sizes: Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
    },
    /// A leaf node containing actual data elements.
    Leaf {
        /// The elements stored in this leaf.
        elements: SmallVec<[T; LEAF_CAPACITY]>,
    },
}

impl<T: Clone> RRBNode<T> {
    pub fn make_relaxed(children: Vec<Arc<RRBNode<T>>>) -> Self {
        let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> = children
            .iter()
            .map(|child| child.calculate_size())
            .collect();

        RRBNode::Branch {
            children: children.into(),
            sizes: Some(sizes),
        }
    }

    pub fn find_child_relaxed(&self, index: usize) -> Option<(usize, usize)> {
        match self {
            RRBNode::Branch {
                sizes: Some(sizes), ..
            } => {
                let mut cumulative = 0;
                for (i, &size) in sizes.iter().enumerate() {
                    if index < cumulative + size {
                        return Some((i, index - cumulative));
                    }
                    cumulative += size;
                }
                None
            },
            _ => self.find_child_regular(index, 1),
        }
    }

    pub fn find_child_regular(&self, index: usize, height: usize) -> Option<(usize, usize)> {
        match self {
            RRBNode::Leaf { .. } => None,
            RRBNode::Branch { children, .. } => {
                let child_capacity = if height == 0 {
                    LEAF_CAPACITY
                } else {
                    LEAF_CAPACITY * BRANCHING_FACTOR.pow(height as u32)
                };

                let child_index = index / child_capacity;
                let sub_index = index % child_capacity;

                if child_index < children.len() {
                    Some((child_index, sub_index))
                } else {
                    None
                }
            },
        }
    }

    pub fn is_relaxed(&self) -> bool {
        matches!(self, RRBNode::Branch { sizes: Some(_), .. })
    }

    pub fn update_size_table_after_removal(
        sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, index: usize,
    ) -> Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>> {
        if let Some(sizes) = sizes {
            let mut new_sizes = sizes.clone();
            if index == 0 {
                new_sizes.remove(0);
            } else {
                new_sizes.pop();
            }
            if new_sizes.is_empty() {
                None
            } else {
                Some(new_sizes)
            }
        } else {
            None
        }
    }

    pub fn update_size_table_after_update(
        sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, index: usize, new_size: usize,
    ) -> Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>> {
        if let Some(sizes) = sizes {
            let mut new_sizes = sizes.clone();
            if index < new_sizes.len() {
                new_sizes[index] = new_size;
            }
            Some(new_sizes)
        } else {
            sizes.clone()
        }
    }

    pub fn create_empty_leaf_result<U>(popped: U) -> Option<(Self, U)> {
        Some((
            RRBNode::Leaf {
                elements: SmallVec::new(),
            },
            popped,
        ))
    }

    pub fn create_branch_result(
        children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        sizes: Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, popped: T,
    ) -> Option<(Self, T)> {
        Some((RRBNode::Branch { children, sizes }, popped))
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        match self {
            RRBNode::Leaf { elements } => elements.get(index),
            RRBNode::Branch { children, .. } => {
                let (child_idx, sub_index) = if self.is_relaxed() {
                    self.find_child_relaxed(index)?
                } else {
                    self.find_child_regular(index, 1)?
                };
                children.get(child_idx)?.get(sub_index)
            },
        }
    }

    pub fn find_child(
        &self, index: usize, sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
    ) -> Option<(usize, usize)> {
        if let Some(sizes) = sizes {
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
            let child_size = LEAF_CAPACITY;
            let child_index = index / child_size;
            let sub_index = index % child_size;
            Some((child_index, sub_index))
        }
    }

    pub fn update(&self, index: usize, value: T) -> Self {
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

    pub fn push_leaf(&self, leaf: Arc<RRBNode<T>>) -> Self {
        match self {
            RRBNode::Leaf { .. } => {
                let self_size = self.calculate_size();
                let leaf_size = leaf.calculate_size();
                let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                    SmallVec::from_iter([self_size, leaf_size]);

                RRBNode::Branch {
                    children: SmallVec::from_iter([Arc::new(self.clone()), leaf]),
                    sizes: Some(sizes),
                }
            },
            RRBNode::Branch { children, sizes } => {
                if children.len() < BRANCHING_FACTOR {
                    let mut new_children = children.clone();
                    new_children.push(leaf.clone());

                    let mut new_sizes = sizes.clone().unwrap_or_else(|| {
                        children
                            .iter()
                            .map(|child| child.calculate_size())
                            .collect()
                    });
                    new_sizes.push(leaf.calculate_size());

                    RRBNode::Branch {
                        children: new_children,
                        sizes: Some(new_sizes),
                    }
                } else {
                    let self_size = self.calculate_size();
                    let leaf_size = leaf.calculate_size();
                    let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                        SmallVec::from_iter([self_size, leaf_size]);

                    RRBNode::Branch {
                        children: SmallVec::from_iter([Arc::new(self.clone()), leaf]),
                        sizes: Some(sizes),
                    }
                }
            },
        }
    }

    pub fn calculate_size(&self) -> usize {
        match self {
            RRBNode::Leaf { elements } => elements.len(),
            RRBNode::Branch { children, sizes } => {
                if let Some(sizes) = sizes {
                    sizes.iter().sum()
                } else {
                    children.iter().map(|child| child.calculate_size()).sum()
                }
            },
        }
    }

    pub fn pop_back(&self) -> Option<(Self, T)> {
        match self {
            RRBNode::Leaf { elements } => {
                if elements.is_empty() {
                    return None;
                }
                let mut new_elements = elements.clone();
                let popped = new_elements.pop()?;
                Some((
                    RRBNode::Leaf {
                        elements: new_elements,
                    },
                    popped,
                ))
            },
            RRBNode::Branch { children, sizes } => {
                if children.is_empty() {
                    return None;
                }

                let last_child_index = children.len() - 1;
                let last_child = &children[last_child_index];

                if let Some((new_child, popped)) = last_child.pop_back() {
                    let mut new_children = children.clone();

                    if new_child.calculate_size() == 0 {
                        new_children.pop();
                        let new_sizes =
                            Self::update_size_table_after_removal(sizes, last_child_index);

                        if new_children.is_empty() {
                            return Self::create_empty_leaf_result(popped);
                        }

                        Self::create_branch_result(new_children, new_sizes, popped)
                    } else {
                        new_children[last_child_index] = Arc::new(new_child);

                        let new_size = new_children[last_child_index].calculate_size();
                        let new_sizes =
                            Self::update_size_table_after_update(sizes, last_child_index, new_size);

                        Some((
                            RRBNode::Branch {
                                children: new_children,
                                sizes: new_sizes,
                            },
                            popped,
                        ))
                    }
                } else {
                    None
                }
            },
        }
    }

    pub fn push_front_leaf(&self, leaf: Arc<RRBNode<T>>) -> Self {
        match self {
            RRBNode::Leaf { .. } => {
                let leaf_size = leaf.calculate_size();
                let self_size = self.calculate_size();
                let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                    SmallVec::from_iter([leaf_size, self_size]);

                RRBNode::Branch {
                    children: SmallVec::from_iter([leaf, Arc::new(self.clone())]),
                    sizes: Some(sizes),
                }
            },
            RRBNode::Branch { children, sizes } => {
                if children.len() < BRANCHING_FACTOR {
                    let mut new_children = SmallVec::with_capacity(children.len() + 1);
                    new_children.push(leaf.clone());
                    new_children.extend(children.iter().cloned());

                    let new_sizes = if let Some(sizes) = sizes {
                        let mut new_sizes = SmallVec::with_capacity(sizes.len() + 1);
                        new_sizes.push(leaf.calculate_size());
                        new_sizes.extend(sizes.iter().cloned());
                        new_sizes
                    } else {
                        let mut new_sizes = SmallVec::with_capacity(children.len() + 1);
                        new_sizes.push(leaf.calculate_size());
                        new_sizes.extend(children.iter().map(|child| child.calculate_size()));
                        new_sizes
                    };

                    RRBNode::Branch {
                        children: new_children,
                        sizes: Some(new_sizes),
                    }
                } else {
                    let leaf_size = leaf.calculate_size();
                    let self_size = self.calculate_size();
                    let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                        SmallVec::from_iter([leaf_size, self_size]);

                    RRBNode::Branch {
                        children: SmallVec::from_iter([leaf, Arc::new(self.clone())]),
                        sizes: Some(sizes),
                    }
                }
            },
        }
    }

    pub fn pop_front(&self) -> Option<(Self, T)> {
        match self {
            RRBNode::Leaf { elements } => {
                if elements.is_empty() {
                    return None;
                }
                let mut new_elements = elements.clone();
                let popped = new_elements.remove(0);
                Some((
                    RRBNode::Leaf {
                        elements: new_elements,
                    },
                    popped,
                ))
            },
            RRBNode::Branch { children, sizes } => {
                if children.is_empty() {
                    return None;
                }

                let first_child = &children[0];

                if let Some((new_child, popped)) = first_child.pop_front() {
                    let mut new_children = children.clone();

                    if new_child.calculate_size() == 0 {
                        new_children.remove(0);
                        let new_sizes = Self::update_size_table_after_removal(sizes, 0);

                        if new_children.is_empty() {
                            return Self::create_empty_leaf_result(popped);
                        }

                        Self::create_branch_result(new_children, new_sizes, popped)
                    } else {
                        new_children[0] = Arc::new(new_child);

                        let new_size = new_children[0].calculate_size();
                        let new_sizes = Self::update_size_table_after_update(sizes, 0, new_size);

                        Some((
                            RRBNode::Branch {
                                children: new_children,
                                sizes: new_sizes,
                            },
                            popped,
                        ))
                    }
                } else {
                    None
                }
            },
        }
    }
}
