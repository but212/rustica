# Doctest Best Practices for Rustica

This document outlines best practices for writing doctests in the Rustica codebase, ensuring consistency and correctness across all documentation.

## General Guidelines

1. **Always include explicit imports** to make tests self-contained:

   ````rust
   /// ```rust
   /// use rustica::prelude::*;
   /// use rustica::datatypes::maybe::Maybe;
   /// // Your code here
   /// ```
   ````

2. **Use explicit type annotations** where needed for clarity, especially with generic types:

   ````rust
   /// ```rust
   /// // GOOD: Explicit type annotation for generic type
   /// let maybe_value: Maybe<i32> = Maybe::just(42);
   ///
   /// // BAD: Ambiguous generic type
   /// let maybe_value = Maybe::just(42); // Type inference could fail
   /// ```
   ````

3. **For static methods with generic types, use turbofish syntax**:

   ````rust
   /// ```rust
   /// // GOOD: Explicit type parameters
   /// let value = Validated::<&str, i32>::pure(42);
   ///
   /// // BAD: Missing type parameters
   /// let value = Validated::pure(42); // Type inference could fail
   /// ```
   ````

4. **Include assertions** to demonstrate expected behavior:

   ````rust
   /// ```rust
   /// assert_eq!(result, expected);
   /// // For enum variants, use matches!
   /// assert!(matches!(result, Maybe::Just(42)));
   /// ```
   ````

5. **Import both the type and its trait** when using trait methods:
   ````rust
   /// ```rust
   /// use rustica::datatypes::maybe::Maybe;
   /// use rustica::traits::functor::Functor; // Import trait to use fmap
   ///
   /// let value = Maybe::just(42);
   /// let result = value.fmap(|x| x * 2);
   /// ```
   ````

## Closure Parameters

When writing doctests for functions that take closures as parameters, pay special attention to closure parameter types:

### Owned vs. Reference Parameters

1. For methods that operate on references (like `fmap`, `bind`), the closure should take reference parameters:
   ````rust
   /// ```rust
   /// // CORRECT:
   /// let result = maybe_value.fmap(|x: &i32| x.to_string());
   ///
   /// // INCORRECT:
   /// let result = maybe_value.fmap(|x: i32| x.to_string());
   /// ```
   ````

### Common Errors

The error "type mismatch in closure arguments" with message like:

```
expected closure signature `fn(_) -> _`
found closure signature `fn(&_) -> _`
```

indicates that the doctest is using a reference parameter when the method expects an owned value, or vice versa.

## Examples for Common Patterns

### Functors (fmap)

````rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::traits::functor::Functor;
///
/// let value = Maybe::just(42);
/// let result = value.fmap(|x: &i32| x * 2);
/// assert_eq!(result, Maybe::just(84));
/// ```
````

### Applicatives (pure, apply)

````rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::traits::applicative::Applicative;
///
/// // Using explicit type for a function in Maybe context
/// let f: Maybe<fn(i32) -> String> = Maybe::just(|x: &i32| x.to_string());
/// let value = Maybe::just(42);
/// let result = value.apply(&f);
/// assert_eq!(result, Maybe::just("42".to_string()));
/// ```
````

### Monads (bind)

````rust
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::traits::monad::Monad;
///
/// let value = Maybe::just(42);
/// let result = value.bind(|x: &i32| {
///     if x > 0 {
///         Maybe::just(x * 2)
///     } else {
///         Maybe::nothing()
///     }
/// });
/// assert_eq!(result, Maybe::just(84));
/// ```
````

### PersistentVector

````rust
/// ```rust
/// use rustica::pvec::PersistentVector;
///
/// // Create a vector
/// let vec1 = PersistentVector::from_slice(&[1, 2, 3]);
///
/// // Modify (creates a new vector)
/// let vec2 = vec1.push_back(4);
///
/// // Original remains unchanged
/// assert_eq!(vec1.len(), 3);
/// assert_eq!(vec2.len(), 4);
/// ```
````

## Testing Performance Characteristics

Include comments about performance implications when appropriate:

````rust
/// ```rust
/// // This operation has O(1) complexity
/// let result = maybe_value.fmap(|x: &i32| x + 1);
///
/// // This chain avoids intermediate allocations
/// let result = value
///     .fmap(|x: &i32| x + 1)
///     .bind(|x: &i32| pure(x.to_string()));
/// ```
````

## Asynchronous Examples

For async code, use `tokio` attribute for testing:

````rust
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
````
