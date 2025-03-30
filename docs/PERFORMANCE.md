# Performance Characteristics of Rustica Types

This document outlines the performance characteristics of various implementations in the Rustica library. Understanding these characteristics can help you make informed decisions about which types to use in performance-sensitive applications.

## Core Types

### Maybe

`Maybe<T>` is a wrapper around Rust's `Option<T>` with additional monadic operations.

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|----------------|------------------|-------|
| `just`/`nothing` | O(1) | O(1) | Constant-time construction |
| `is_just`/`is_nothing` | O(1) | O(1) | Simple enum variant check |
| `and_then` | O(1) | O(1) + f | Where f is the complexity of the binding function |
| `unwrap` | O(1) | O(1) | Panics if `Nothing` |
| `value_or` | O(1) | O(1) | Returns default if `Nothing` |

**Memory Overhead**: One word (usize) for enum discriminant plus size of contained value

**Best Used For**:
- Representing optional values
- Chaining computations that might fail
- API boundaries where absence of a value is meaningful

### Either

`Either<L, R>` represents a value of one of two possible types (similar to `Result<R, L>` but with more monadic operations).

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|----------------|------------------|-------|
| `left`/`right` | O(1) | O(1) | Constant-time construction |
| `is_left`/`is_right` | O(1) | O(1) | Simple enum variant check |
| `fmap_right` | O(1) | O(1) + f | Maps only on the Right variant |
| `fmap_left` | O(1) | O(1) + f | Maps only on the Left variant |
| `and_then` | O(1) | O(1) + f | Binds only on the Right variant |
| `value_or` | O(1) | O(1) | Returns Right value or default |

**Memory Overhead**: One word (usize) for enum discriminant plus size of contained value (either L or R)

**Best Used For**:
- Error handling with rich error types
- Computations that may fail with error details
- Representing disjoint unions in domain modeling

### Id

`Id<T>` is a simple identity monad that wraps a value.

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|----------------|------------------|-------|
| `new` | O(1) | O(1) | Constant-time construction |
| `into_inner` | O(1) | O(1) | Unwraps the internal value |
| `and_then` | O(1) | O(1) + f | Where f is the complexity of the binding function |

**Memory Overhead**: Size of contained value plus potential alignment padding

**Best Used For**:
- Type-level programming where a monad interface is required
- Testing monad laws
- Educational purposes to understand the simplest monad implementation

### AsyncM

`AsyncM<A>` represents an asynchronous computation that will eventually produce a value.

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|----------------|------------------|-------|
| `new`/`pure` | O(1) | O(1) | Constant-time construction |
| `try_get` | O(f) | O(f) | Where f is the complexity of the wrapped async function |
| `fmap` | O(1) | O(1) | Adds a transformation to be executed when the future resolves |
| `bind` | O(1) | O(1) | Chains another async computation |
| `zip_with` | O(max(f,g)) | O(f+g) | Runs two async computations in parallel |

**Memory Overhead**: Size of `Arc<dyn Fn() -> BoxFuture<'static, A>>` plus task scheduler overhead

**Best Used For**:
- Functional-style async programming
- Composing complex async workflows
- Maintaining referential transparency in async contexts

## Monad Transformers

### StateT

`StateT<S, M, A>` adds stateful computations to any monad M.

| Operation | Time Complexity | Space Complexity | Notes |
|-----------|----------------|------------------|-------|
| `new` | O(1) | O(1) | Constant-time construction |
| `run_state` | O(f) | O(f) | Where f is the complexity of the state function |
| `fmap` | O(1) | O(1) | Adds a transformation to the result |
| `and_then` | O(1) | O(1) | Chains another state computation |
| `get` | O(1) | O(1) | Creates a computation that returns the current state |
| `put` | O(1) | O(1) | Creates a computation that updates the state |
| `modify` | O(1) | O(1) + f | Creates a computation that modifies the state |

**Memory Overhead**: Function closure size + underlying monad overhead

**Best Used For**:
- Managing state in a pure functional way
- Composing stateful operations
- Combining state with other effects (e.g., Maybe, Either)

## Performance Optimizations

### Chain Optimization

When chaining operations like `fmap` and `and_then`, Rustica types try to minimize intermediate allocations:

```rust
// More efficient:
let result = value
    .fmap(|x| x + 1)
    .fmap(|x| x.to_string());

// Less efficient (but semantically equivalent):
let intermediate = value.fmap(|x| x + 1);
let result = intermediate.fmap(|x| x.to_string());
```

### Ownership vs. References

Rustica prefers taking ownership where appropriate to avoid unnecessary cloning, but still provides reference-based methods for flexibility:

- Methods often take `self` rather than `&self` when the operation logically consumes the input
- Methods that accept closures use appropriate bounds (`FnOnce` vs. `Fn`) depending on whether the closure should take ownership

Example:
```rust
// Takes ownership of the value:
let result = maybe_value.fmap(|x| x * 2);

// Clones the value and preserves the original:
let result = maybe_value.clone().fmap(|x| x * 2);
```

## Memory Usage Considerations

### Stack vs. Heap Allocation

- Most Rustica types store their values directly (stack allocation) when possible
- Complex types like `AsyncM` use heap allocation via `Arc` for shared ownership
- When values are large, consider using references in your transformations to avoid copying

### Avoiding Common Pitfalls

1. **Unnecessary Cloning**: Prefer taking ownership with `self` methods when you don't need the original value
2. **Boxing Large Values**: For large values in monadic contexts, consider using boxed values or references
3. **Nested Monads**: Deeply nested monadic structures can lead to complex types and performance overhead; use monad transformers instead

## Benchmarking

The Rustica library includes benchmarks for core operations. You can run them with:

```bash
cargo bench --features advanced -- "either|id|maybe"
```

Or run all benchmarks with:

```bash
cargo bench --features advanced
```

## Performance Comparison with Standard Library

| Operation | Rustica Type | Std Library Equivalent | Relative Performance |
|-----------|--------------|------------------------|----------------------|
| `Maybe::fmap` | `Maybe<T>` | `Option<T>::map` | Comparable |
| `Either::fmap` | `Either<L, R>` | `Result<R, L>::map` | Comparable |
| `AsyncM::fmap` | `AsyncM<A>` | `Future::then` | Small overhead for monadic interface |

In most cases, Rustica's performance characteristics are similar to the standard library equivalents, with slight overhead due to the more flexible interface and additional functionality.
