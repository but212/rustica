use crate::prelude::Functor;

/// Applies a transformation to all values in a vector.
///
/// # Arguments
///
/// * `values`: The vector of values to transform
/// * `f`: The transformation function
///
/// # Returns
///
/// A new vector containing the transformed values
#[inline]
pub fn transform_all<T, F, U>(values: &[T], f: F) -> Vec<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U + Copy,
    U: Clone,
{
    values.iter().map(|v| v.fmap(f)).collect()
}

/// Applies a transformation to a single value.
///
/// # Arguments
///
/// * `value`: The value to transform
/// * `f`: The transformation function
///
/// # Returns
///
/// The transformed value, or `None` if the input value was `None`
#[inline]
pub fn transform_chain<T, F, U>(value: Option<T>, f: F) -> Option<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U,
    U: Clone,
{
    value.map(|v| v.fmap(f))
}

/// A pipeline is a sequence of transformations applied to a value.
pub struct Pipeline<T>(T);

impl<T> Pipeline<T> {
    /// Creates a new pipeline with the given value.
    ///
    /// # Arguments
    ///
    /// * `value`: The initial value for the pipeline
    ///
    /// # Returns
    ///
    /// A new pipeline containing the value
    #[inline]
    pub fn new(value: T) -> Self {
        Pipeline(value)
    }

    /// Extracts the final value from the pipeline.
    ///
    /// # Returns
    ///
    /// The transformed value
    #[inline]
    pub fn extract(self) -> T {
        self.0
    }
}

impl<T: Functor> Pipeline<T> {
    #[inline]
    pub fn map_owned<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.fmap_owned(f))
    }

    #[inline]
    pub fn map<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(&T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.fmap(f))
    }
}
