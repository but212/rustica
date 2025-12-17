# Either Typeclass Cleanup Guide

## Overview

Version 0.11.0 removes the `MonadPlus` implementation from `Either<L, R>` to clarify its categorical semantics.

---

## Breaking Change

### MonadPlus Implementation Removed

```rust
// REMOVED in v0.11.0
impl<L, R> MonadPlus for Either<L, R> { ... }
```

**Why**: `MonadPlus` implies a notion of "zero" and "plus" that doesn't fit `Either`'s semantics well. Use `Alternative` for left-biased or right-biased choice semantics instead.

---

## Migration

### Using Alternative

```rust
// OLD (v0.10.x)
use rustica::traits::monad_plus::MonadPlus;
let result = either1.mplus(&either2);

// NEW (v0.11.0)
use rustica::traits::alternative::Alternative;
let result = either1.alt(&either2);
```

### Choice Semantics

`Alternative::alt` for `Either<L, R>` provides right-biased choice:

- If `self` is `Right`, return `self`
- If `self` is `Left`, return `other`

```rust
use rustica::datatypes::either::Either;
use rustica::traits::alternative::Alternative;

let left: Either<&str, i32> = Either::Left("error");
let right: Either<&str, i32> = Either::Right(42);

// Right-biased: returns first Right, or last Left
assert_eq!(left.alt(&right), Either::Right(42));
assert_eq!(right.alt(&left), Either::Right(42));
```

---

## Either Core API

The following operations remain unchanged:

```rust
// Construction
Either::Left(l)
Either::Right(r)

// Access
either.left()           // Option<&L>
either.right()          // Option<&R>
either.unwrap()         // R (panics if Left)
either.unwrap_or(def)   // R with default

// Transformation
either.map_left(f)      // Transform Left
either.map_right(f)     // Transform Right (same as fmap)
either.fmap(f)          // Functor
either.bind(f)          // Monad
either.bimap(f, g)      // Transform both sides

// Categorical traits
either.alt(&other)      // Alternative (right-biased choice)
either.combine(&other)  // Semigroup
```

---

## Summary

| Removed | Reason | Migration |
|---------|--------|-----------|
| `MonadPlus` | Unclear semantics for Either | Use `Alternative::alt()` |

`Either<L, R>` remains a powerful sum type with clear Functor/Monad/Alternative semantics.
