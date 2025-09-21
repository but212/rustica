use super::node::{BRANCHING_FACTOR, LEAF_CAPACITY, RRBNode, SMALL_SIZE_TABLE_SIZE};
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
            self.root.get(adjusted_index)
        } else {
            let tail_index = adjusted_index - tree_size;
            self.tail.get(tail_index)
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

        Self {
            root: Arc::new(new_root),
            tail: SmallVec::new(),
            head: self.head.clone(),
            height: self.height,
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

        Self {
            root: Arc::new(new_root),
            tail: self.tail.clone(),
            head: SmallVec::new(),
            height: self.height,
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

        let mut left_elements = Vec::new();
        let mut right_elements = Vec::new();

        left_elements.extend(self.head.iter().cloned());
        let self_tree_size = self.len - self.head.len() - self.tail.len();
        for i in 0..self_tree_size {
            if let Some(elem) = self.root.get(i) {
                left_elements.push(elem.clone());
            }
        }
        left_elements.extend(self.tail.iter().cloned());

        right_elements.extend(other.head.iter().cloned());
        let other_tree_size = other.len - other.head.len() - other.tail.len();
        for i in 0..other_tree_size {
            if let Some(elem) = other.root.get(i) {
                right_elements.push(elem.clone());
            }
        }
        right_elements.extend(other.tail.iter().cloned());

        left_elements.extend(right_elements);
        Self::from_elements(left_elements.into_iter())
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
        let first_element = self.get(0)?.clone();

        let tree_size = self.len - self.head.len() - self.tail.len();
        if tree_size > 0
            && let Some((new_root, _)) = self.root.pop_front()
        {
            return Some((
                Self {
                    root: Arc::new(new_root),
                    tail: self.tail.clone(),
                    head: self.head.clone(),
                    height: self.height,
                    len: self.len - 1,
                },
                first_element,
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
            return (
                Self {
                    root: Arc::new(RRBNode::Leaf {
                        elements: SmallVec::new(),
                    }),
                    tail: SmallVec::new(),
                    head: SmallVec::new(),
                    height: 0,
                    len: 0,
                },
                self.clone(),
            );
        }
        if index >= self.len {
            return (
                self.clone(),
                Self {
                    root: Arc::new(RRBNode::Leaf {
                        elements: SmallVec::new(),
                    }),
                    tail: SmallVec::new(),
                    head: SmallVec::new(),
                    height: 0,
                    len: 0,
                },
            );
        }

        let mut left_elements = Vec::new();
        let mut right_elements = Vec::new();

        let mut current_index = 0;

        for elem in &self.head {
            if current_index < index {
                left_elements.push(elem.clone());
            } else {
                right_elements.push(elem.clone());
            }
            current_index += 1;
        }

        let tree_size = self.len - self.head.len() - self.tail.len();
        for i in 0..tree_size {
            if let Some(elem) = self.root.get(i) {
                if current_index < index {
                    left_elements.push(elem.clone());
                } else {
                    right_elements.push(elem.clone());
                }
                current_index += 1;
            }
        }

        for elem in &self.tail {
            if current_index < index {
                left_elements.push(elem.clone());
            } else {
                right_elements.push(elem.clone());
            }
            current_index += 1;
        }

        (
            Self::from_elements(left_elements.into_iter()),
            Self::from_elements(right_elements.into_iter()),
        )
    }
}
