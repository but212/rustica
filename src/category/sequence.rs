use crate::category::hkt::{HKT, TypeConstraints};
use crate::category::traversable::Traversable;
use crate::category::applicative::Applicative;
use crate::fntype::{FnType, FnTrait};

/// A trait for types that can be sequenced.
/// This trait provides a way to sequence a structure of effects into an effect of structure.
/// 
/// For example:
/// - `Vec<Option<T>>` -> `Option<Vec<T>>`
/// - `Vec<Result<T, E>>` -> `Result<Vec<T>, E>`
/// 
/// # Type Parameters
/// * `A` - The type of elements in the structure
/// 
/// # Laws
/// A Sequence instance must satisfy these laws:
/// 1. Naturality: For any natural transformation `η: F ~> G` and sequence `xs`,
///    `η(sequence(xs)) = sequence(fmap(η)(xs))`
/// 2. Identity: For any sequence `xs`,
///    `sequence(fmap(pure)(xs)) = pure(xs)`
/// 3. Composition: For nested sequences `xss`,
///    `sequence(sequence(xss)) = sequence(fmap(sequence)(xss))`
pub trait Sequence<A>: Traversable<A>
where
    A: TypeConstraints,
{
    /// Evaluate each action in sequence from left to right, and collect the results.
    /// This is equivalent to `traverse(identity)`.
    fn sequence<F>(self) -> F::Output<Self::Output<A>>
    where
        F: HKT + Applicative<A> + TypeConstraints,
        F::Output<A>: TypeConstraints,
        Self: Sized,
    {
        self.traverse::<F, A, _>(FnType::new(F::pure))
    }
}

// Blanket implementation for any type that implements Traversable
impl<T, A> Sequence<A> for T 
where
    T: Traversable<A>,
    A: TypeConstraints,
{
}

/// Sequence a vector of Results into a Result of vector
/// 
/// # Type Parameters
/// * `T` - The type to be sequenced.
/// * `E` - The error type.
///
/// Returns
/// * `Result<Vec<T>, E>` - The result of the sequence.
pub fn sequence_result<T, E>(items: Vec<Result<T, E>>) -> Result<Vec<T>, E>
where
    T: TypeConstraints,
    E: TypeConstraints,
{
    let mut result = Vec::new();
    for item in items {
        match item {
            Ok(value) => result.push(value),
            Err(e) => return Err(e),
        }
    }
    Ok(result)
}

/// Sequence a vector of Options into an Option of vector
/// 
/// # Type Parameters
/// * `T` - The type to be sequenced.
///
/// Returns
/// * `Option<Vec<T>>` - The result of the sequence.
pub fn sequence_option<T>(items: Vec<Option<T>>) -> Option<Vec<T>>
where
    T: TypeConstraints,
{
    let mut result = Vec::new();
    for item in items {
        match item {
            Some(value) => result.push(value),
            None => return None,
        }
    }
    Some(result)
}