use smallvec::SmallVec;
use std::fmt::{self, Debug};
use std::sync::Arc;

use super::error::PVecError;
use super::iter::{PersistentVectorIntoIter, PersistentVectorIter};
use super::tree::RRBTree;

pub const ADAPTIVE_INLINE_SIZE: usize = 64;

type Generation = u32;

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

impl<T> PersistentVector<T> {
    pub fn new() -> Self {
        Self {
            inner: VectorImpl::Inline {
                elements: SmallVec::new(),
            },
            len: 0,
            generation: 0,
        }
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

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn iter(&self) -> PersistentVectorIter<'_, T> {
        PersistentVectorIter {
            vector: self,
            position: 0,
        }
    }
}

impl<T: Clone> PersistentVector<T> {
    pub fn from_slice(slice: &[T]) -> Self {
        Self::from_iter(slice.iter().cloned())
    }

    pub fn map<U, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U,
        U: Clone,
    {
        PersistentVector::from_iter(self.iter().map(f))
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.as_ref().get(index),
        }
    }

    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        Self::from_iter(self.iter().filter(|x| predicate(x)).cloned())
    }

    pub fn try_get(&self, index: usize) -> Result<&T, PVecError> {
        self.get(index).ok_or(PVecError::IndexOutOfBounds {
            index,
            len: self.len,
        })
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

    pub fn filter_map<U: Clone, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> Option<U>,
    {
        PersistentVector::from_iter(self.iter().filter_map(f))
    }

    pub fn flat_map<U: Clone, F, I>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> I,
        I: IntoIterator<Item = U>,
    {
        PersistentVector::from_iter(self.iter().flat_map(f))
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

    pub fn sorted(&self) -> Self
    where
        T: Ord,
    {
        let mut items: Vec<T> = self.iter().cloned().collect();
        items.sort();
        Self::from_iter(items)
    }

    pub fn fold<B, F>(&self, init: B, f: F) -> B
    where
        F: Fn(B, &T) -> B,
    {
        self.iter().fold(init, f)
    }

    pub fn zip<U>(&self, other: &PersistentVector<U>) -> PersistentVector<(T, U)>
    where
        U: Clone,
    {
        PersistentVector::from_iter(
            self.iter()
                .zip(other.iter())
                .map(|(a, b)| (a.clone(), b.clone())),
        )
    }

    pub fn partition<F>(&self, predicate: F) -> (Self, Self)
    where
        F: Fn(&T) -> bool,
    {
        let mut true_items = Vec::new();
        let mut false_items = Vec::new();

        for item in self.iter() {
            if predicate(item) {
                true_items.push(item.clone());
            } else {
                false_items.push(item.clone());
            }
        }

        (Self::from_iter(true_items), Self::from_iter(false_items))
    }

    pub fn chunk(&self, size: usize) -> PersistentVector<PersistentVector<T>> {
        if size == 0 {
            return PersistentVector::new();
        }

        PersistentVector::from_iter(
            self.iter()
                .collect::<Vec<_>>()
                .chunks(size)
                .map(|chunk| PersistentVector::from_iter(chunk.iter().map(|&x| x.clone()))),
        )
    }

    pub fn with_cache_policy<P>(_policy: P) -> Self {
        Self::new()
    }

    pub fn from_slice_with_cache_policy<P>(slice: &[T], _policy: P) -> Self {
        Self::from_slice(slice)
    }

    pub fn push_back(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
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
                    self.transition_to_tree().push_back(value)
                }
            },
            VectorImpl::Tree { tree: _ } => self.tree_push_back(value),
        }
    }

    pub fn push_front(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
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
                    self.transition_to_tree().push_front(value)
                }
            },
            VectorImpl::Tree { tree: _ } => self.tree_push_front(value),
        }
    }

    pub fn try_update(&self, index: usize, value: T) -> Result<Self, PVecError> {
        if index >= self.len {
            return Err(PVecError::IndexOutOfBounds {
                index,
                len: self.len,
            });
        }
        Ok(self.update(index, value))
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
                let iter = left.iter().chain(right.iter()).cloned();
                Self::from_iter(iter)
            },
            (VectorImpl::Inline { elements }, VectorImpl::Tree { tree }) => {
                let left_tree = RRBTree::from_elements(elements.iter().cloned());
                let merged_tree = left_tree.concat(tree);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(merged_tree),
                    },
                    len: self.len + other.len,
                    generation: self.generation + 1,
                }
            },
            (VectorImpl::Tree { tree }, VectorImpl::Inline { elements }) => {
                let right_tree = RRBTree::from_elements(elements.iter().cloned());
                let merged_tree = tree.concat(&right_tree);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(merged_tree),
                    },
                    len: self.len + other.len,
                    generation: self.generation + 1,
                }
            },
            (VectorImpl::Tree { .. }, VectorImpl::Tree { .. }) => {
                let left_tree = self.ensure_tree();
                let right_tree = other.ensure_tree();
                let merged_tree = left_tree.concat(&right_tree);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Arc::new(merged_tree),
                    },
                    len: self.len + other.len,
                    generation: self.generation + 1,
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

    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }
}

impl<T: Clone> Default for PersistentVector<T> {
    fn default() -> Self {
        Self::new()
    }
}

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
