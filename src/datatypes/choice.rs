use std::sync::Arc;

use crate::traits::{
    hkt::{TypeOps, AnyBox, HKT},
    pure::Pure,
    functor::Functor,
    applicative::Applicative, 
    monad::Monad,
    arrow::Arrow,
    composable::Composable,
    identity::Identity,
    bifunctor::Bifunctor,
    foldable::Foldable,
    semigroup::Semigroup,
    monoid::Monoid,
    category::Category,
};

/// Represents a choice between multiple values of the same type.
///
/// `Choice<T>` encapsulates a primary value and a list of alternative values.
/// It provides methods to manipulate and query these values.
///
/// # Type Parameters
///
/// * `T`: The type of the values, which must implement `TypeOps`, `Clone`, `Default`, `Send`, and `Sync`.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::choice::Choice;
/// use std::sync::Arc;
///
/// // Basic usage
/// let mut choice = Choice::new(1);
/// choice.add_alternative(2);
/// choice.add_alternative(3);
///
/// assert_eq!(*choice.value(), 1);
/// assert!(choice.has_alternatives());
///
/// // Functor
/// let mapped = choice.fmap(Arc::new(|x| *x.downcast_ref::<i32>().unwrap() * 2));
/// assert_eq!(*mapped.downcast_ref::<Choice<i32>>().unwrap().value(), 2);
///
/// // Applicative
/// let f = Choice::new(|x: i32| x + 1);
/// let result = choice.apply(Arc::new(|f| f.downcast_ref::<Box<dyn Fn(i32) -> i32>>().unwrap()(1)));
/// assert_eq!(*result.downcast_ref::<Choice<i32>>().unwrap().value(), 2);
///
/// // Monad
/// let bound = choice.bind(Arc::new(|x| Arc::new(Choice::new(*x.downcast_ref::<i32>().unwrap() * 3)) as Arc<dyn Any + Send + Sync>));
/// assert_eq!(*bound.downcast_ref::<Choice<i32>>().unwrap().value(), 3);
/// ```
#[derive(Debug, Clone)]
pub struct Choice<T: TypeOps + Clone + Default + Send + Sync + 'static> {
    value: T,
    alternatives: Vec<T>,
}

impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Choice<T> {
    /// Creates a new `Choice` with the given value and no alternatives.
    ///
    /// # Arguments
    ///
    /// * `value` - The primary value for this `Choice`.
    pub fn new(value: T) -> Self {
        Self { value, alternatives: Vec::new() }
    }

    /// Creates a new `Choice` with the given value and alternatives.
    ///
    /// # Arguments
    ///
    /// * `value` - The primary value for this `Choice`.
    /// * `alternatives` - A vector of alternative values.
    pub fn with_alternatives(value: T, alternatives: Vec<T>) -> Self {
        Self { value, alternatives }
    }

    /// Returns a reference to the current primary value.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Returns a slice of the alternative values.
    pub fn alternatives(&self) -> &[T] {
        &self.alternatives
    }

    /// Adds a new alternative value.
    ///
    /// # Arguments
    ///
    /// * `alt` - The alternative value to add.
    pub fn add_alternative(&mut self, alt: T) {
        self.alternatives.push(alt);
    }

    /// Moves to the next alternative, if any.
    ///
    /// Returns `true` if there was a next alternative, `false` otherwise.
    pub fn next(&mut self) -> bool {
        if let Some(next_value) = self.alternatives.pop() {
            self.alternatives.push(std::mem::replace(&mut self.value, next_value));
            true
        } else {
            false
        }
    }

    /// Checks if there are any alternatives.
    ///
    /// Returns `true` if there are alternatives, `false` otherwise.
    pub fn has_alternatives(&self) -> bool {
        !self.alternatives.is_empty()
    }
}


impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Semigroup for Choice<T> {
    fn combine(&self, other: AnyBox) -> AnyBox {
        if let Some(other_choice) = other.downcast_ref::<Self>() {
            Arc::new(Choice {
                value: self.value.clone(),
                alternatives: self.alternatives.iter().chain(other_choice.alternatives.iter()).cloned().collect(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }
}

impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Monoid for Choice<T> {
    fn empty(&self) -> AnyBox {
        Arc::new(Choice::new(T::default())) as AnyBox
    }
}

impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Category for Choice<T> {
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(other_choice) = other.downcast_ref::<Self>() {
            Arc::new(Choice {
                value: other_choice.value.clone(),
                alternatives: self.alternatives.iter().chain(&other_choice.alternatives).cloned().collect(),
            }) as AnyBox
        } else {
            Arc::new(self.clone()) as AnyBox
        }
    }

    fn identity_morphism() -> AnyBox {
        Arc::new(Choice::new(T::default())) as AnyBox
    }
}

// Identity implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Identity for Choice<T> {
    fn identity() -> AnyBox {
        Arc::new(Choice::new(T::default())) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(Choice::new(T::default())) as AnyBox)
    }
}

// Higher-kinded type implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> HKT for Choice<T> {
    fn apply_type(&self) -> AnyBox {
        Arc::new(self.clone()) as AnyBox
    }

    fn downcast(&self, boxed: &AnyBox) -> Option<AnyBox> {
        boxed.downcast_ref::<Self>().map(|x| Arc::new(x.clone()) as AnyBox)
    }
}

// Pure implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Pure for Choice<T> {
    fn pure(value: AnyBox) -> AnyBox {
        if let Some(val) = value.downcast_ref::<T>() {
            Arc::new(Choice::new(val.clone())) as AnyBox
        } else {
            Arc::new(Choice::new(T::default())) as AnyBox
        }
    }
}

// Functor implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Functor for Choice<T> {
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mapped_value = f(Arc::new(self.value.clone()) as AnyBox);
        let mapped_alts: Vec<T> = self.alternatives.iter()
            .filter_map(|alt| {
                let boxed = Arc::new(alt.clone()) as AnyBox;
                let mapped = f(boxed);
                mapped.downcast_ref::<T>().cloned()
            })
            .collect();

        Arc::new(Choice::with_alternatives(
            mapped_value.downcast_ref().cloned().unwrap_or_else(|| T::default()),
            mapped_alts
        )) as AnyBox
    }
}

// Applicative implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Applicative for Choice<T> {
    fn apply(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let value = self.value.clone_box();
        let result = f(value);
        let mut alternatives = Vec::new();
        for alt in &self.alternatives {
            alternatives.push(f(alt.clone_box()));
        }
        Arc::new(Choice::with_alternatives(
            result.downcast_ref::<T>().unwrap().clone(),
            alternatives.into_iter()
                .map(|x| x.downcast_ref::<T>().unwrap().clone())
                .collect()
        )) as AnyBox
    }

    fn lift2(&self, other: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let Some(other_choice) = other.downcast_ref::<Self>() {
            let lifted = f(
                Arc::new(self.value.clone()) as AnyBox,
                Arc::new(other_choice.value.clone()) as AnyBox
            );
            
            let mut alts = Vec::new();
            for alt1 in &self.alternatives {
                for alt2 in &other_choice.alternatives {
                    let result = f(
                        Arc::new(alt1.clone()) as AnyBox,
                        Arc::new(alt2.clone()) as AnyBox
                    );
                    if let Some(val) = result.downcast_ref::<T>() {
                        alts.push(val.clone());
                    }
                }
            }

            Arc::new(Choice::with_alternatives(
                lifted.downcast_ref().cloned().unwrap_or_default(),
                alts
            )) as AnyBox
        } else {
            Self::pure(other)
        }
    }

    fn lift3(&self, b: AnyBox, c: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        if let (Some(choice_b), Some(choice_c)) = (b.downcast_ref::<Self>(), c.downcast_ref::<Self>()) {
            let lifted = f(
                Arc::new(self.value.clone()) as AnyBox,
                Arc::new(choice_b.value.clone()) as AnyBox,
                Arc::new(choice_c.value.clone()) as AnyBox
            );
            
            let mut alts = Vec::new();
            for alt1 in &self.alternatives {
                for alt2 in &choice_b.alternatives {
                    for alt3 in &choice_c.alternatives {
                        let result = f(
                            Arc::new(alt1.clone()) as AnyBox,
                            Arc::new(alt2.clone()) as AnyBox,
                            Arc::new(alt3.clone()) as AnyBox
                        );
                        if let Some(val) = result.downcast_ref::<T>() {
                            alts.push(val.clone());
                        }
                    }
                }
            }

            Arc::new(Choice::with_alternatives(
                lifted.downcast_ref().cloned().unwrap_or_default(),
                alts
            )) as AnyBox
        } else {
            Self::pure(b)
        }
    }
}

// Monad implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Monad for Choice<T> {
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let bound = f(Arc::new(self.value.clone()) as AnyBox);
        let mut alts = Vec::new();
        
        for alt in &self.alternatives {
            let result = f(Arc::new(alt.clone()) as AnyBox);
            if let Some(choice) = result.downcast_ref::<Self>() {
                alts.extend(choice.alternatives.clone());
                alts.push(choice.value.clone());
            }
        }

        if let Some(choice) = bound.downcast_ref::<Self>() {
            Arc::new(Choice::with_alternatives(
                choice.value.clone(),
                alts
            )) as AnyBox
        } else {
            Arc::new(Choice::with_alternatives(
                bound.downcast_ref().cloned().unwrap_or_default(),
                alts
            )) as AnyBox
        }
    }

    fn join(&self) -> AnyBox {
        let mut alts = Vec::new();
        
        for alt in &self.alternatives {
            if let Some(choice) = (Arc::new(alt.clone()) as AnyBox).downcast_ref::<Self>() {
                alts.extend(choice.alternatives.clone());
                alts.push(choice.value.clone());
            } else {
                alts.push(alt.clone());
            }
        }

        if let Some(choice) = (Arc::new(self.value.clone()) as AnyBox).downcast_ref::<Self>() {
            Arc::new(Choice::with_alternatives(
                choice.value.clone(),
                alts
            )) as AnyBox
        } else {
            Arc::new(Choice::with_alternatives(
                self.value.clone(),
                alts
            )) as AnyBox
        }
    }
}

// Arrow implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Arrow for Choice<T> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        if let Some(func) = f.downcast_ref::<Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>>() {
            let value_box: AnyBox = Arc::new(self.value.clone());
            let result = func(value_box);
            if let Some(value) = result.downcast_ref::<T>() {
                Arc::new(Choice::new(value.clone())) as AnyBox
            } else {
                Arc::new(Choice::new(T::default())) as AnyBox
            }
        } else {
            Arc::new(Choice::new(T::default())) as AnyBox
        }
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        self.arrow(f)
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        self.arrow(f)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        let result1 = self.arrow(f);
        let result2 = self.arrow(g);
        
        if let (Some(choice1), Some(choice2)) = (
            result1.downcast_ref::<Self>(),
            result2.downcast_ref::<Self>()
        ) {
            let mut alts = choice1.alternatives.clone();
            alts.extend(choice2.alternatives.clone());
            
            Arc::new(Choice::with_alternatives(
                choice1.value.clone(),
                alts
            )) as AnyBox
        } else {
            Arc::new(Choice::new(T::default())) as AnyBox
        }
    }
}

// Composable implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Composable for Choice<T> {
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let composed = f(Arc::new(self.value.clone()) as AnyBox);
        let mut alts = Vec::new();
        
        for alt in &self.alternatives {
            let result = f(Arc::new(alt.clone()) as AnyBox);
            if let Some(val) = result.downcast_ref::<T>() {
                alts.push(val.clone());
            }
        }

        Arc::new(Choice::with_alternatives(
            composed.downcast_ref().cloned().unwrap_or_default(),
            alts
        )) as AnyBox
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

// Bifunctor implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Bifunctor for Choice<T> {
    fn bimap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let value = self.value.clone();
        let alternatives = self.alternatives.clone();
        
        let mapped_value = if let Some(result) = f(Arc::new(value) as AnyBox).downcast_ref::<T>() {
            result.clone()
        } else {
            T::default()
        };

        let mapped_alternatives = alternatives.into_iter().map(|alt| {
            if let Some(result) = g(Arc::new(alt) as AnyBox).downcast_ref::<T>() {
                result.clone()
            } else {
                T::default()
            }
        }).collect();

        Arc::new(Choice {
            value: mapped_value,
            alternatives: mapped_alternatives,
        }) as AnyBox
    }

    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(f, Arc::new(|x| x))
    }

    fn map_second(&self, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        self.bimap(Arc::new(|x| x), g)
    }
}

// Foldable implementation
impl<T: TypeOps + Clone + Default + Send + Sync + 'static> Foldable for Choice<T> {
    fn fold_left(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut acc = init;
        acc = f(acc.clone(), Arc::new(self.value.clone()) as AnyBox);
        
        for alt in &self.alternatives {
            acc = f(acc.clone(), Arc::new(alt.clone()) as AnyBox);
        }
        
        acc
    }

    fn fold_right(&self, init: AnyBox, f: Arc<dyn Fn(AnyBox, AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut acc = init;
        
        for alt in self.alternatives.iter().rev() {
            acc = f(Arc::new(alt.clone()) as AnyBox, acc.clone());
        }
        
        f(Arc::new(self.value.clone()) as AnyBox, acc)
    }

    fn fold_map(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut values = Vec::new();
        values.push(f(Arc::new(self.value.clone()) as AnyBox));
        
        for alt in &self.alternatives {
            values.push(f(Arc::new(alt.clone()) as AnyBox));
        }
        
        Arc::new(values) as AnyBox
    }
}
