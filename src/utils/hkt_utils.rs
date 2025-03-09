// Sequence implementation for Option
pub fn sequence_option<A>(collection: Vec<Option<A>>) -> Option<Vec<A>> {
    let mut result = Vec::new();
    
    for item in collection {
        match item {
            Some(a) => result.push(a),
            None => return None,
        }
    }
    
    Some(result)
}

// Sequence implementation for Result
pub fn sequence_result<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    let mut result = Vec::new();
    
    for item in collection {
        match item {
            Ok(a) => result.push(a),
            Err(e) => return Err(e),
        }
    }
    
    Ok(result)
}

// Traverse implementation for Option
pub fn traverse_option<A, B, F>(
    collection: impl IntoIterator<Item = A>,
    f: F
) -> Option<Vec<B>>
where
    F: Fn(A) -> Option<B>
{
    let mut result = Vec::new();
    
    for item in collection {
        match f(item) {
            Some(b) => result.push(b),
            None => return None,
        }
    }
    
    Some(result)
}

// Traverse implementation for Result
pub fn traverse_result<A, B, E, F>(
    collection: impl IntoIterator<Item = A>,
    f: F
) -> Result<Vec<B>, E>
where
    F: Fn(A) -> Result<B, E>
{
    let mut result = Vec::new();
    
    for item in collection {
        match f(item) {
            Ok(b) => result.push(b),
            Err(e) => return Err(e),
        }
    }
    
    Ok(result)
}

// Generic filter_map implementation
pub fn filter_map<A, B, C, P, F>(collection: C, predicate: P, f: F) -> Vec<B>
where
    C: IntoIterator<Item = A>,
    P: Fn(&A) -> bool,
    F: Fn(A) -> B,
{
    collection
        .into_iter()
        .filter(predicate)
        .map(f)
        .collect()
}

// Pipeline implementation for Option
pub fn pipeline_option<A, B, Func>(
    initial: A,
    operations: Vec<Func>
) -> Option<B>
where
    Func: Fn(B) -> Option<B>,
    A: Into<B>,
{
    let mut iter = operations.into_iter();
    
    // Handle the first operation or just use the initial value
    let initial_result = match iter.next() {
        Some(first_op) => first_op(initial.into()),
        None => Some(initial.into()),
    };
    
    // Apply the remaining operations
    iter.fold(initial_result, |acc, op| {
        match acc {
            Some(value) => op(value),
            None => None,
        }
    })
}

// Pipeline implementation for Result
pub fn pipeline_result<A, B, E, Func>(
    initial: A,
    operations: Vec<Func>
) -> Result<B, E>
where
    Func: Fn(B) -> Result<B, E>,
    A: Into<B>,
{
    let mut iter = operations.into_iter();
    
    // Handle the first operation or just use the initial value
    let initial_result = match iter.next() {
        Some(first_op) => first_op(initial.into()),
        None => Ok(initial.into()),
    };
    
    // Apply the remaining operations
    iter.fold(initial_result, |acc, op| {
        match acc {
            Ok(value) => op(value),
            Err(e) => Err(e),
        }
    })
}

// Utility functions for Option
#[inline]
pub fn lift_option<A, B, F>(f: F) -> impl Fn(Option<A>) -> Option<B>
where
    F: Fn(A) -> B,
{
    move |opt| opt.map(&f)
}

// Utility functions for Result
#[inline]
pub fn map_result<A, B, E, F>(result: Result<A, E>, f: F) -> Result<B, E>
where
    F: Fn(A) -> B,
{
    result.map(f)
}

// Try pipeline for Result
#[inline]
pub fn try_pipeline<A, B, E, F>(initial: A, operations: Vec<F>) -> Result<B, E>
where
    F: Fn(B) -> Result<B, E>,
    A: Into<B>,
{
    pipeline_result(initial, operations)
}

// Apply multiple operations to a single input
#[inline]
pub fn fan_out<A: Clone, B, F>(input: A, operations: Vec<F>) -> Vec<B>
where
    F: Fn(A) -> B,
{
    operations
        .into_iter()
        .map(|op| op(input.clone()))
        .collect()
}

// Combine elements from two collections
#[inline]
pub fn zip_with<A, B, C, F>(xs: Vec<A>, ys: Vec<B>, f: F) -> Vec<C>
where
    F: Fn(A, B) -> C,
{
    xs.into_iter()
        .zip(ys)
        .map(|(x, y)| f(x, y))
        .collect()
}

// Compose multiple transformations
#[inline]
pub fn compose_all<A, B>(transformations: Vec<Box<dyn Fn(A) -> A>>) -> Box<dyn Fn(A) -> B>
where
    A: 'static,
    B: 'static + From<A>,
{
    Box::new(move |input| {
        let result = transformations.iter().fold(input, |acc, f| f(acc));
        B::from(result)
    })
}