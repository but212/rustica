use crate::category::hkt::ReturnTypeConstraints;
use crate::category::monad::Monad;

/// A trait for types that can be sequenced.
/// 
/// # Type Parameters
/// * `T` - The type to be sequenced.
/// * `M` - The monad to be used for sequencing.
///
/// # Laws
/// A Sequence instance must satisfy these laws:
/// 1. Naturality: For any natural transformation `η: F ~> G` and sequence `xs`,
///    `η(sequence(xs)) = sequence(map(η)(xs))`
/// 2. Identity: For any sequence `xs`,
///    `sequence(map(pure)(xs)) = pure(xs)`
/// 3. Composition: For nested sequences `xss`,
///    `sequence(sequence(xss)) = sequence(map(sequence)(xss))`
/// 4. Monad Consistency: For any monadic value `m` and function `f`,
///    `sequence(pure(m)) = map(pure)(m)`
/// 5. Order Preservation: For any sequence `xs`,
///    The order of effects in `sequence(xs)` must match the order in `xs`
/// 6. Failure Propagation (for fallible types):
///    - For `Option`: If any element is `None`, the result is `None`
///    - For `Result`: If any element is `Err(e)`, the result is `Err(e)`
pub trait Sequence<T, M>: Monad<T>
where
    T: ReturnTypeConstraints,
    M: Monad<T>,
{
    /// Evaluate each action in sequence from left to right, and collect the results.
    /// 
    /// # Type Parameters
    /// * `A` - The type to be sequenced.
    ///
    /// Returns
    /// * `Self::Output<Vec<A>>` - The result of the sequence.
    fn sequence<A>(self) -> Self::Output<Vec<A>>
    where
        A: ReturnTypeConstraints,
        M: Monad<A> + Monad<Vec<A>>,
        M::Output<A>: ReturnTypeConstraints,
        M::Output<Vec<A>>: ReturnTypeConstraints,
        T: Into<M>;
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
    T: ReturnTypeConstraints,
    E: ReturnTypeConstraints,
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
    T: ReturnTypeConstraints,
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
