use super::node::{
    BRANCHING_FACTOR, LEAF_CAPACITY, RRBNode, SMALL_BRANCH_SIZE, SMALL_SIZE_TABLE_SIZE,
};
use smallvec::SmallVec;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RRBTree<T> {
    pub root: Arc<RRBNode<T>>,
    pub tail: SmallVec<[T; LEAF_CAPACITY]>,
    pub head: SmallVec<[T; LEAF_CAPACITY]>,
    pub height: usize,
    pub len: usize,
}

impl<T: Clone> RRBTree<T> {
    pub fn from_elements<I: Iterator<Item = T>>(elements: I) -> Self {
        let elements: Vec<T> = elements.collect();

        let len = elements.len();
        if len <= LEAF_CAPACITY {
            Self {
                root: Arc::new(RRBNode::Leaf {
                    elements: SmallVec::from_iter(elements),
                }),
                tail: SmallVec::new(),
                head: SmallVec::new(),
                height: 0,
                len,
            }
        } else {
            Self::build_tree_with_tail(elements)
        }
    }

    fn build_tree_with_tail(elements: Vec<T>) -> Self {
        let total_len = elements.len();

        let tree_elements_len = (total_len / LEAF_CAPACITY) * LEAF_CAPACITY;
        let tree_elements = &elements[..tree_elements_len];
        let tail_elements = &elements[tree_elements_len..];

        if tree_elements.is_empty() {
            Self {
                root: Arc::new(RRBNode::Leaf {
                    elements: SmallVec::new(),
                }),
                tail: SmallVec::from_iter(tail_elements.iter().cloned()),
                head: SmallVec::new(),
                height: 0,
                len: total_len,
            }
        } else {
            let mut leaves = Vec::new();
            for chunk in tree_elements.chunks(LEAF_CAPACITY) {
                let leaf = RRBNode::Leaf {
                    elements: SmallVec::from_iter(chunk.iter().cloned()),
                };
                leaves.push(Arc::new(leaf));
            }

            let (root, height) = Self::build_tree_recursive(leaves);

            Self {
                root,
                tail: SmallVec::from_iter(tail_elements.iter().cloned()),
                head: SmallVec::new(),
                height,
                len: total_len,
            }
        }
    }

    fn build_tree_recursive(nodes: Vec<Arc<RRBNode<T>>>) -> (Arc<RRBNode<T>>, usize) {
        if nodes.len() == 1 {
            return (nodes.into_iter().next().unwrap(), 0);
        }

        let mut next_level = Vec::new();

        for chunk in nodes.chunks(BRANCHING_FACTOR) {
            let children = SmallVec::from_iter(chunk.iter().cloned());

            let sizes: SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]> = children
                .iter()
                .map(|child: &Arc<RRBNode<T>>| child.calculate_size())
                .collect();

            let branch = RRBNode::Branch {
                children,
                sizes: Some(sizes),
            };
            next_level.push(Arc::new(branch));
        }

        let (root, sub_height) = Self::build_tree_recursive(next_level);
        (root, sub_height + 1)
    }

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
        let mut current_height = self.height;

        loop {
            match current_node.as_ref() {
                RRBNode::Leaf { elements } => {
                    return elements.get(remaining_index);
                },
                RRBNode::Branch { children, sizes } => {
                    let (child_idx, sub_index) = if sizes.is_some() {
                        current_node.find_child_relaxed(remaining_index)?
                    } else {
                        let child_height = current_height.saturating_sub(1);
                        current_node.find_child_regular(remaining_index, child_height)?
                    };

                    current_node = children.get(child_idx)?;
                    remaining_index = sub_index;
                    current_height = current_height.saturating_sub(1);
                },
            }
        }
    }

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

        let tail_leaf = RRBNode::Leaf {
            elements: self.tail.clone(),
        };

        let new_root = self.root.push_leaf(Arc::new(tail_leaf));
        let new_height = Self::calculate_height(&Arc::new(new_root.clone()));

        Self {
            root: Arc::new(new_root),
            tail: SmallVec::new(),
            head: self.head.clone(),
            height: new_height,
            len: self.len,
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

        let head_leaf = RRBNode::Leaf {
            elements: self.head.clone(),
        };

        let new_root = self.root.push_front_leaf(Arc::new(head_leaf));
        let new_height = Self::calculate_height(&Arc::new(new_root.clone()));

        Self {
            root: Arc::new(new_root),
            tail: self.tail.clone(),
            head: SmallVec::new(),
            height: new_height,
            len: self.len,
        }
    }

    pub fn concat(&self, other: &Self) -> Self {
        if self.len == 0 {
            return other.clone();
        }
        if other.len == 0 {
            return self.clone();
        }

        if self.height == other.height {
            self.concat_same_height(other)
        } else if self.height < other.height {
            other.concat_different_height(self, false)
        } else {
            self.concat_different_height(other, true)
        }
    }

    fn concat_same_height(&self, other: &Self) -> Self {
        let mut left_for_merge = self.clone();
        let mut right_for_merge = other.clone();

        if !left_for_merge.tail.is_empty() {
            left_for_merge = left_for_merge.push_tail_to_tree();
        }

        if !right_for_merge.head.is_empty() {
            right_for_merge = right_for_merge.push_head_to_tree();
        }

        let merged_root = Self::concat_nodes(
            &left_for_merge.root,
            &right_for_merge.root,
            self.height.max(other.height),
        );

        Self {
            root: Arc::new(merged_root),
            tail: right_for_merge.tail.clone(),
            head: left_for_merge.head.clone(),
            height: self.height.max(other.height),
            len: self.len + other.len,
        }
    }

    fn concat_different_height(&self, other: &Self, left_higher: bool) -> Self {
        if left_higher {
            let elevated_other = Self::elevate_tree(other, self.height);
            self.concat_same_height(&elevated_other)
        } else {
            let elevated_self = Self::elevate_tree(self, other.height);
            elevated_self.concat_same_height(other)
        }
    }

    fn elevate_tree(tree: &Self, target_height: usize) -> Self {
        let mut current_root = tree.root.clone();
        let mut current_height = tree.height;

        while current_height < target_height {
            let new_root = RRBNode::Branch {
                children: SmallVec::from_iter([current_root.clone()]),
                sizes: Some(SmallVec::from_iter([current_root.calculate_size()])),
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

    fn concat_nodes(left: &Arc<RRBNode<T>>, right: &Arc<RRBNode<T>>, height: usize) -> RRBNode<T> {
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
                    RRBNode::Leaf { elements: combined }
                } else {
                    let mid = LEAF_CAPACITY;
                    let left_part = SmallVec::from_iter(combined.iter().take(mid).cloned());
                    let right_part = SmallVec::from_iter(combined.iter().skip(mid).cloned());

                    RRBNode::make_relaxed(vec![
                        Arc::new(RRBNode::Leaf {
                            elements: left_part,
                        }),
                        Arc::new(RRBNode::Leaf {
                            elements: right_part,
                        }),
                    ])
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

                for i in 0..left_children.len().saturating_sub(1) {
                    new_children.push(left_children[i].clone());
                }

                if let (Some(left_last), Some(right_first)) =
                    (left_children.last(), right_children.first())
                {
                    let next_height = height.saturating_sub(1);
                    let merged_middle = Self::concat_nodes(left_last, right_first, next_height);
                    new_children.push(Arc::new(merged_middle));
                }

                for i in 1..right_children.len() {
                    new_children.push(right_children[i].clone());
                }

                RRBNode::make_relaxed(new_children)
            },
            (RRBNode::Leaf { .. }, RRBNode::Branch { .. })
            | (RRBNode::Branch { .. }, RRBNode::Leaf { .. }) => {
                let left_as_branch = match left.as_ref() {
                    RRBNode::Leaf { .. } => vec![left.clone()],
                    RRBNode::Branch { children, .. } => children.iter().cloned().collect(),
                };

                let right_as_branch = match right.as_ref() {
                    RRBNode::Leaf { .. } => vec![right.clone()],
                    RRBNode::Branch { children, .. } => children.iter().cloned().collect(),
                };

                let mut all_children = left_as_branch;
                all_children.extend(right_as_branch);

                RRBNode::make_relaxed(all_children)
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
            self.pop_from_tree()
        }
    }

    fn pop_from_tree(&self) -> Option<(Self, T)> {
        if self.len == 0 {
            return None;
        }

        let tree_size = self.len - self.tail.len();
        if tree_size == 0 {
            return None;
        }

        let last_tree_index = tree_size - 1;
        let last_element = self.root.get(last_tree_index)?.clone();

        let (new_root, new_height) = if tree_size == 1 {
            (
                Arc::new(RRBNode::Leaf {
                    elements: SmallVec::new(),
                }),
                0,
            )
        } else {
            match self.root.pop_back() {
                Some((new_root, _)) => (Arc::new(new_root), self.height),
                None => (self.root.clone(), self.height),
            }
        };

        Some((
            Self {
                root: new_root,
                tail: self.tail.clone(),
                head: self.head.clone(),
                height: new_height,
                len: self.len - 1,
            },
            last_element,
        ))
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
            return Some((
                Self {
                    root: Arc::new(new_root),
                    tail: self.tail.clone(),
                    head: self.head.clone(),
                    height: self.height,
                    len: self.len - 1,
                },
                popped_element,
            ));
        }

        if !self.tail.is_empty() {
            let mut new_head = SmallVec::new();
            for item in self.tail.iter().rev() {
                new_head.push(item.clone());
            }
            let popped = new_head.pop()?;

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
                    let child_height = current_height.saturating_sub(1);
                    let adjusted_index = self.calculate_adjusted_index(
                        target_index,
                        child_index,
                        sizes,
                        child_height,
                    );

                    let next_height = current_height.saturating_sub(1);
                    let (left_child, right_child) =
                        self.split_along_path(remaining_path, adjusted_index, child, next_height);

                    let left_branch =
                        self.create_left_branch(children, child_index, left_child, sizes);
                    let right_branch =
                        self.create_right_branch(children, child_index, right_child, sizes);

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
                let left_elements = SmallVec::from_iter(elements.iter().take(index).cloned());
                let right_elements = SmallVec::from_iter(elements.iter().skip(index).cloned());

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
        _sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
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
        _sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>,
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
        sizes: &Option<SmallVec<[usize; SMALL_SIZE_TABLE_SIZE]>>, height: usize,
    ) -> usize {
        if let Some(sizes) = sizes {
            let mut cumulative = 0;
            for i in 0..child_index {
                cumulative += sizes.get(i).unwrap_or(&0);
            }
            target_index.saturating_sub(cumulative)
        } else {
            let child_capacity = if height <= 1 {
                LEAF_CAPACITY
            } else {
                LEAF_CAPACITY * BRANCHING_FACTOR.pow((height - 1) as u32)
            };
            target_index.saturating_sub(child_index * child_capacity)
        }
    }

    fn find_path_to_index(&self, index: usize) -> Vec<usize> {
        let mut path = Vec::new();
        let mut current_node = &self.root;
        let mut remaining_index = index;
        let mut current_height = self.height;

        while current_height > 0 {
            match current_node.as_ref() {
                RRBNode::Branch { children, sizes } => {
                    let (child_idx, sub_index) = if sizes.is_some() {
                        current_node
                            .find_child_relaxed(remaining_index)
                            .unwrap_or((0, 0))
                    } else {
                        let child_height = current_height.saturating_sub(1);
                        current_node
                            .find_child_regular(remaining_index, child_height)
                            .unwrap_or((0, 0))
                    };

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
