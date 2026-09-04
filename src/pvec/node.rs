//! Internal RRB tree node implementation.
//!
//! This module contains the core node structure for the RRB (Relaxed Radix Balanced) tree
//! that underlies the persistent vector implementation.
//!
//! # Architecture
//!
//! The RRB tree uses two types of nodes:
//!
//! - **Branch nodes**: Internal nodes containing references to child nodes
//! - **Leaf nodes**: Terminal nodes containing actual data elements
//!
//! # Relaxed Balancing
//!
//! Unlike standard radix balanced trees, RRB trees allow nodes to have varying
//! numbers of children. This "relaxation" enables efficient concatenation and
//! splitting operations while maintaining good performance for random access.
//!
//! When a tree becomes "relaxed" (irregular), branch nodes store a size table
//! to enable O(log n) index lookups despite the irregular structure.

use smallvec::SmallVec;
use std::sync::Arc;

/// Maximum number of children per branch node.
///
/// This value (32) is chosen to balance tree height with cache efficiency.
/// A branching factor of 32 means the tree height grows as log₃₂(n).
pub(crate) const BRANCHING_FACTOR: usize = 32;

pub(crate) const LEAF_CAPACITY: usize = 64;

pub(crate) const SMALL_BRANCH_SIZE: usize = 8;

pub(crate) const SMALL_SIZE_TABLE_SIZE: usize = 8;

/// A node in the RRB tree structure.
///
/// RRB nodes can be either branch nodes (containing child nodes) or leaf nodes
/// (containing actual data elements). Branch nodes may have a size table for
/// relaxed balancing when the tree becomes irregular.
///
/// # Structural Sharing
///
/// Nodes are wrapped in `Arc` to enable structural sharing between different
/// versions of the tree. When a node is modified, only the path from the root
/// to that node needs to be copied (path copying), while unchanged subtrees
/// are shared.
///
/// # Memory Layout
///
/// - Branch nodes use `SmallVec` with inline storage for up to 8 children
/// - Leaf nodes use `SmallVec` with inline storage for up to 64 elements
/// - Size tables (when present) also use `SmallVec` with inline storage
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RRBNode<T> {
    /// A branch node containing child nodes.
    ///
    /// Branch nodes form the internal structure of the tree, with each child
    /// being either another branch or a leaf node.
    Branch {
        /// Child nodes of this branch.
        ///
        /// The number of children is bounded by `BRANCHING_FACTOR` (32).
        children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        /// Optional size table for relaxed balancing.
        ///
        /// When `Some`, contains cumulative sizes of each subtree, enabling
        /// O(log n) index lookups in irregular trees. When `None`, the tree
        /// is regular and index calculation uses arithmetic.
        sizes: Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
    },
    /// A leaf node containing actual data elements.
    ///
    /// Leaf nodes are the terminal nodes of the tree and store the actual
    /// vector elements.
    Leaf {
        /// The elements stored in this leaf.
        ///
        /// The number of elements is bounded by `LEAF_CAPACITY` (64).
        elements: SmallVec<[T; LEAF_CAPACITY]>,
    },
}

/// Read-only methods that don't require Clone
impl<T> RRBNode<T> {
    /// Finds the child index and sub-index for a relaxed (irregular) tree.
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

    /// Finds the child index and sub-index for a regular (balanced) tree.
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

    /// Calculates the total size (number of elements) in this subtree.
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
}

/// Node transformation and update methods
impl<T: Clone> RRBNode<T> {
    pub fn create_branch_result(
        children: SmallVec<[Arc<RRBNode<T>>; SMALL_BRANCH_SIZE]>,
        sizes: Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, popped: T,
    ) -> Option<(Self, T)> {
        Some((RRBNode::Branch { children, sizes }, popped))
    }

    pub fn update(&self, index: usize, value: T, current_height: usize) -> Self {
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
                let found = if sizes.is_some() {
                    self.find_child_relaxed(index)
                } else {
                    let child_height = current_height.saturating_sub(1);
                    self.find_child_regular(index, child_height)
                };

                if let Some((child_index, sub_index)) = found {
                    if let Some(child) = children.get(child_index) {
                        let child_height = current_height.saturating_sub(1);
                        let updated_child = child.update(sub_index, value, child_height);
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

    pub fn update_size_table_after_removal(
        sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, index: usize,
    ) -> Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>> {
        if let Some(sizes) = sizes {
            let mut new_sizes = sizes.clone();
            if index < new_sizes.len() {
                new_sizes.remove(index);
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

    fn append_size(
        children: &[Arc<RRBNode<T>>], sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
        new_size: usize,
    ) -> SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> {
        if let Some(s) = sizes {
            let mut ns = s.clone();
            ns.push(new_size);
            ns
        } else {
            let mut ns: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                children.iter().map(|c| c.calculate_size()).collect();
            ns.push(new_size);
            ns
        }
    }

    fn prepend_size(
        children: &[Arc<RRBNode<T>>], sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
        new_size: usize,
    ) -> SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> {
        if let Some(s) = sizes {
            let mut ns = SmallVec::with_capacity(s.len() + 1);
            ns.push(new_size);
            ns.extend(s.iter().cloned());
            ns
        } else {
            let mut ns = SmallVec::with_capacity(children.len() + 1);
            ns.push(new_size);
            ns.extend(children.iter().map(|c| c.calculate_size()));
            ns
        }
    }

    fn replace_size_at(
        children: &[Arc<RRBNode<T>>], sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
        index: usize, new_size: usize,
    ) -> SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> {
        if let Some(s) = sizes {
            let mut ns = s.clone();
            ns[index] = new_size;
            ns
        } else {
            let mut ns: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> =
                children.iter().map(|c| c.calculate_size()).collect();
            ns[index] = new_size;
            ns
        }
    }

    /// Recursively inserts a leaf node at the back of a subtree at the given height.
    ///
    /// - If the insertion succeeds within the current subtree, returns `Ok(new_node)`.
    /// - If the subtree overflows, returns `Err(new_sibling)` where `new_sibling` is at the same
    ///   height as `node`, containing the inserted elements.
    pub fn push_back_leaf_recursive(
        node: &Arc<RRBNode<T>>, leaf: Arc<RRBNode<T>>, height: usize,
    ) -> Result<Arc<RRBNode<T>>, Arc<RRBNode<T>>> {
        let RRBNode::Branch { children, sizes } = node.as_ref() else {
            let leaf_size = leaf.calculate_size();
            let new_sibling = Arc::new(RRBNode::Branch {
                children: SmallVec::from_iter([leaf]),
                sizes: Some(SmallVec::from_iter([leaf_size])),
            });
            return Err(new_sibling);
        };

        let leaf_size = leaf.calculate_size();
        if height <= 1 {
            if children.len() < BRANCHING_FACTOR {
                let mut new_children = children.clone();
                new_children.push(leaf);
                let new_sizes = Self::append_size(children, sizes, leaf_size);
                Ok(Arc::new(RRBNode::Branch {
                    children: new_children,
                    sizes: Some(new_sizes),
                }))
            } else {
                let new_sibling = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([leaf]),
                    sizes: Some(SmallVec::from_iter([leaf_size])),
                });
                Err(new_sibling)
            }
        } else {
            if children.is_empty() {
                let child = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([leaf.clone()]),
                    sizes: Some(SmallVec::from_iter([leaf_size])),
                });
                return Ok(Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([child.clone()]),
                    sizes: Some(SmallVec::from_iter([child.calculate_size()])),
                }));
            }

            let last_idx = children.len() - 1;
            match Self::push_back_leaf_recursive(&children[last_idx], leaf, height - 1) {
                Ok(new_last_child) => {
                    let mut new_children = children.clone();
                    let child_size = new_last_child.calculate_size();
                    new_children[last_idx] = new_last_child;
                    let new_sizes = Self::replace_size_at(children, sizes, last_idx, child_size);
                    Ok(Arc::new(RRBNode::Branch {
                        children: new_children,
                        sizes: Some(new_sizes),
                    }))
                },
                Err(new_sibling) => {
                    let sibling_size = new_sibling.calculate_size();
                    if children.len() < BRANCHING_FACTOR {
                        let mut new_children = children.clone();
                        new_children.push(new_sibling);
                        let new_sizes = Self::append_size(children, sizes, sibling_size);
                        Ok(Arc::new(RRBNode::Branch {
                            children: new_children,
                            sizes: Some(new_sizes),
                        }))
                    } else {
                        let new_branch = Arc::new(RRBNode::Branch {
                            children: SmallVec::from_iter([new_sibling]),
                            sizes: Some(SmallVec::from_iter([sibling_size])),
                        });
                        Err(new_branch)
                    }
                },
            }
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

    /// Recursively inserts a leaf node at the front of a subtree at the given height.
    ///
    /// - If the insertion succeeds within the current subtree, returns `Ok(new_node)`.
    /// - If the subtree overflows, returns `Err(new_sibling)` where `new_sibling` is at the same
    ///   height as `node`, containing the inserted elements.
    pub fn push_front_leaf_recursive(
        node: &Arc<RRBNode<T>>, leaf: Arc<RRBNode<T>>, height: usize,
    ) -> Result<Arc<RRBNode<T>>, Arc<RRBNode<T>>> {
        let RRBNode::Branch { children, sizes } = node.as_ref() else {
            let leaf_size = leaf.calculate_size();
            let new_sibling = Arc::new(RRBNode::Branch {
                children: SmallVec::from_iter([leaf]),
                sizes: Some(SmallVec::from_iter([leaf_size])),
            });
            return Err(new_sibling);
        };

        let leaf_size = leaf.calculate_size();
        if height <= 1 {
            if children.len() < BRANCHING_FACTOR {
                let mut new_children = SmallVec::with_capacity(children.len() + 1);
                new_children.push(leaf);
                new_children.extend(children.iter().cloned());
                let new_sizes = Self::prepend_size(children, sizes, leaf_size);
                Ok(Arc::new(RRBNode::Branch {
                    children: new_children,
                    sizes: Some(new_sizes),
                }))
            } else {
                let new_sibling = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([leaf]),
                    sizes: Some(SmallVec::from_iter([leaf_size])),
                });
                Err(new_sibling)
            }
        } else {
            if children.is_empty() {
                let child = Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([leaf.clone()]),
                    sizes: Some(SmallVec::from_iter([leaf_size])),
                });
                return Ok(Arc::new(RRBNode::Branch {
                    children: SmallVec::from_iter([child.clone()]),
                    sizes: Some(SmallVec::from_iter([child.calculate_size()])),
                }));
            }

            match Self::push_front_leaf_recursive(&children[0], leaf, height - 1) {
                Ok(new_first_child) => {
                    let mut new_children = children.clone();
                    let child_size = new_first_child.calculate_size();
                    new_children[0] = new_first_child;
                    let new_sizes = Self::replace_size_at(children, sizes, 0, child_size);
                    Ok(Arc::new(RRBNode::Branch {
                        children: new_children,
                        sizes: Some(new_sizes),
                    }))
                },
                Err(new_sibling) => {
                    let sibling_size = new_sibling.calculate_size();
                    if children.len() < BRANCHING_FACTOR {
                        let mut new_children = SmallVec::with_capacity(children.len() + 1);
                        new_children.push(new_sibling);
                        new_children.extend(children.iter().cloned());
                        let new_sizes = Self::prepend_size(children, sizes, sibling_size);
                        Ok(Arc::new(RRBNode::Branch {
                            children: new_children,
                            sizes: Some(new_sizes),
                        }))
                    } else {
                        let new_branch = Arc::new(RRBNode::Branch {
                            children: SmallVec::from_iter([new_sibling]),
                            sizes: Some(SmallVec::from_iter([sibling_size])),
                        });
                        Err(new_branch)
                    }
                },
            }
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
