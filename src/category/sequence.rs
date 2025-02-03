use crate::category::hkt::ReturnTypeConstraints;
use crate::category::monad::Monad;

/// A trait for types that can be sequenced.
pub trait Sequence<T, M>: Monad<T>
where
    T: ReturnTypeConstraints,
    M: Monad<T>,
{
    /// Evaluate each action in sequence from left to right, and collect the results.
    fn sequence<A>(self) -> Self::Output<Vec<A>>
    where
        A: ReturnTypeConstraints,
        M: Monad<A> + Monad<Vec<A>>,
        M::Output<A>: ReturnTypeConstraints,
        M::Output<Vec<A>>: ReturnTypeConstraints,
        T: Into<M>;

    /// Transform a list of values into a list of actions, evaluate these actions from left to right,
    /// and collect the results.
    fn traverse<A, F>(self, f: F) -> Self::Output<Vec<A>>
    where
        A: ReturnTypeConstraints,
        M: Monad<A> + Monad<Vec<A>>,
        M::Output<A>: ReturnTypeConstraints,
        M::Output<Vec<A>>: ReturnTypeConstraints,
        F: FnMut(T) -> M::Output<A>;
}

/// Sequence a vector of Results into a Result of vector
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
