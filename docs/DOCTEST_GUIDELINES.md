# Doctest Best Practices for Rustica

This document outlines best practices for writing doctests in the Rustica codebase, ensuring consistency and correctness across all documentation.

## General Guidelines

1. **Always include explicit imports** to make tests self-contained:
   ```rust
   /// ```rust
   /// use rustica::prelude::*;
   /// use rustica::datatypes::maybe::Maybe;
   /// // Your code here
   /// ```
   ```

2. **Use explicit type annotations** where needed for clarity:
   ```rust
   /// ```rust
   /// let maybe_value: Maybe<i32> = Maybe::just(42);
   /// ```
   ```

3. **Include assertions** to demonstrate expected behavior:
   ```rust
   /// ```rust
   /// assert_eq!(result, expected);
   /// ```
   ```

## Closure Parameters

When writing doctests for functions that take closures as parameters, pay special attention to closure parameter types:

### Owned vs. Reference Parameters

1. For methods that consume values (like `map`, `and_then`), the closure should take owned values:
   ```rust
   /// ```rust
   /// // CORRECT:
   /// let result = maybe_value.map(|x: i32| x.to_string());
   /// 
   /// // INCORRECT:
   /// let result = maybe_value.map(|x: &i32| x.to_string());
   /// ```
   ```

2. Check the method signature to determine if it's taking ownership:
   - Methods that take `self` (not `&self`) usually expect closures that take ownership of inner values
   - These methods typically use `FnOnce(T) -> U` bounds, not `Fn(&T) -> U` bounds

### Common Errors

The error "type mismatch in closure arguments" with message like:
```
expected closure signature `fn(_) -> _`
found closure signature `fn(&_) -> _`
```
indicates that the doctest is using a reference parameter when the method expects an owned value, or vice versa.

## Examples for Common Patterns

### Functors (map)

```rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// 
/// let value = Maybe::just(42);
/// let result = value.map(|x| x * 2);
/// assert_eq!(result, Maybe::just(84));
/// ```
```

### Applicatives (pure, apply)

```rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// 
/// let value = Maybe::just(42);
/// let f = Maybe::just(|x: i32| x.to_string());
/// let result = value.apply(f);
/// assert_eq!(result, Maybe::just("42".to_string()));
/// ```
```

### Monads (bind/and_then)

```rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// 
/// let value = Maybe::just(42);
/// let result = value.and_then(|x| {
///     if x > 0 {
///         Maybe::just(x * 2)
///     } else {
///         Maybe::nothing()
///     }
/// });
/// assert_eq!(result, Maybe::just(84));
/// ```
```

## Testing Performance Characteristics

Include comments about performance implications when appropriate:

```rust
/// ```rust
/// // This operation has O(1) complexity
/// let result = maybe_value.map(|x| x + 1);
/// 
/// // This chain avoids intermediate allocations
/// let result = value
///     .map(|x| x + 1)
///     .map(|x| x.to_string());
/// ```
```

## Asynchronous Examples

For async code, use `tokio` attribute for testing:

```rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::async_monad::AsyncM;
/// 
/// #[tokio::main]
/// async fn main() {
///     let async_value = AsyncM::pure(42);
///     let result = async_value.try_get().await;
///     assert_eq!(result, 42);
/// }
/// ```
```
