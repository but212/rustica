# Migration Guide: v0.11.0

## Breaking Changes: Identity Trait Removal & Unify to unwrap()

### Overview

Version 0.11.0 removes the incorrect `Functor: Identity` dependency and deprecates the `Identity` trait entirely. This is a **breaking change** that aligns Rustica with proper category theory principles **and unifies all value extraction to standard `unwrap()` methods**.

---

## What Changed?

### Before (v0.10.x)

```rust
pub trait Functor: Identity {  // ❌ Wrong dependency
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>;
}
```

### After (v0.11.0)

```rust
pub trait Functor: HKT {  // O Correct - no Identity
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>;
}

#[deprecated(since = "0.11.0", note = "Use unwrap(), as_ref(), or Comonad::extract()")]
pub trait Identity: HKT {
    fn value(&self) -> &Self::Source;
    // ...
}
```

---

## Why This Change?

### Category Theory Violations & Inconsistent API

1. **Functor ≠ Value Extraction**
   - Functors map morphisms: `fmap: (A → B) → F(A) → F(B)`
   - They don't need value extraction
   - Example: `Vec<T>` is a functor but extracting "the" value is meaningless

2. **Name Confusion**
   - "Identity" in category theory = Identity functor `Id(A) = A`
   - Rustica's `Identity` = value extraction utility
   - These are completely different concepts

3. **Inconsistent Value Extraction API**

  ```rust
   // BEFORE: Multiple different ways to extract values
   option.value()              // Identity trait
   maybe.get_value()           // Custom method
   choice.primary_value()      // Custom method
   either.right_value()        // Custom method
   
   // AFTER: Unified to standard unwrap()
   option.unwrap()             // O Standard
   maybe.unwrap()              // O Standard
   choice.unwrap()             // O Standard
   either.unwrap()             // O Standard
   ```

1. **Redundant Abstraction**

   ```rust
   // Identity methods just wrap standard Rust
   option.value()          // Same as option.unwrap()
   option.try_value()      // Same as option.as_ref()
   option.into_value()     // Same as option.unwrap()
   option.try_into_value() // Same as option itself
   ```

2. **Comonad Overlap**

   ```rust
   // Comonad already provides proper extraction
   id.extract()  // Total function (always succeeds)
   id.value()    // Partial function (may panic) - deprecated
   ```

---

## Migration Steps

### Step 1: Remove `Identity` Trait Usage

#### Option A: Use Standard Methods (Recommended)

```rust
// BEFORE (v0.10.x)
use rustica::traits::identity::Identity;

let option = Some(42);
let value = option.value();           // ❌ Deprecated
let safe = option.try_value();        // ❌ Deprecated
let owned = option.into_value();      // ❌ Deprecated

// AFTER (v0.11.0)
let option = Some(42);
let value = option.unwrap();          // O Standard Rust
let safe = option.as_ref();           // O Standard Rust
let owned = option.unwrap();          // O Standard Rust
```

#### Option B: Use Comonad for Total Extraction

```rust
// BEFORE
use rustica::traits::identity::Identity;
let id = Id::new(42);
let value = id.value();               // ❌ Deprecated

// AFTER
use rustica::traits::comonad::Comonad;
let id = Id::new(42);
let value = id.extract();             // O Comonad (always succeeds)
```

### Step 2: Remove Identity Bounds

```rust
// BEFORE
fn process<F>(functor: F) -> F::Output<String>
where
    F: Functor + Identity,  // ❌ Identity no longer needed
{
    functor.fmap(|x| format!("{:?}", x))
}

// AFTER
fn process<F>(functor: F) -> F::Output<String>
where
    F: Functor,  // O Just Functor
{
    functor.fmap(|x| format!("{:?}", x))
}
```

### Step 3: Update Custom Types

If you implemented `Identity` for your types:

```rust
// BEFORE
impl<T> Identity for MyWrapper<T> {
    fn value(&self) -> &Self::Source {
        &self.0
    }
    fn into_value(self) -> Self::Source {
        self.0
    }
}

// AFTER - Option A: Remove Identity (if not needed)
// Just implement Functor, no Identity needed

// AFTER - Option B: Use Comonad (if total extraction)
impl<T: Clone> Comonad for MyWrapper<T> {
    fn extract(&self) -> Self::Source {
        self.0.clone()  // Always succeeds
    }
    fn duplicate(&self) -> Self {
        self.clone()
    }
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U,
    {
        MyWrapper(f(self))
    }
}

// AFTER - Option C: Keep Identity (with deprecation warnings)
#[allow(deprecated)]
impl<T> Identity for MyWrapper<T> {
    // ... same as before
}
```

---

## Common Scenarios

### Scenario 1: Working with Option/Result

```rust
// BEFORE
use rustica::traits::identity::Identity;

fn get_value(opt: Option<i32>) -> i32 {
    opt.value()  // ❌ Deprecated
}

// AFTER
fn get_value(opt: Option<i32>) -> i32 {
    opt.unwrap()  // O Standard
}

// Or better yet:
fn get_value(opt: Option<i32>) -> Result<i32, &'static str> {
    opt.ok_or("No value")  // O Error handling
}
```

### Scenario 1.1: Using Standard unwrap() Methods for All Types

For consistency, use standard Rust `unwrap()` methods for all types:

```rust
// For Maybe<T>
use rustica::datatypes::maybe::Maybe;

let maybe = Maybe::Just(42);
let value = maybe.unwrap();      // T (panics if Nothing)
let safe = maybe.unwrap_or(&0);  // &T with default
let option = maybe.as_option();  // Option<&T> for safe handling

// For Choice<T>
use rustica::datatypes::choice::Choice;

let choice = Choice::new(1, vec![2, 3]);
let value = choice.unwrap();           // T (panics if empty)
let safe = choice.unwrap_or(&0);       // &T with default
let first = choice.first();            // Option<&T>

// For Either<L, R>
use rustica::datatypes::either::Either;

let either: Either<String, i32> = Either::Right(42);
let value = either.unwrap();           // i32 (panics if Left)
let safe = either.unwrap_or(&0);       // &i32 with default
let right = either.right();            // Option<&i32>
let left = either.left();              // Option<&String>

// For types with Comonad (like Id<T>)
use rustica::datatypes::id::Id;
use rustica::traits::comonad::Comonad;

let id = Id::new(42);
let value = id.extract();  // Always succeeds - total extraction
// OR use standard method:
let value = id.unwrap();   // Also works - same as extract()
```

### Scenario 2: Functor Operations

```rust
// BEFORE
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;

fn double<F>(f: F) -> i32
where
    F: Functor + Identity,
    F::Source: Into<i32>,
{
    let mapped = f.fmap(|x| (*x).into() * 2);
    mapped.into_value()  // ❌ Deprecated
}

// AFTER
use rustica::traits::functor::Functor;

fn double<F>(f: F) -> F::Output<i32>
where
    F: Functor,
    F::Source: Into<i32> + Clone,
{
    f.fmap(|x| (*x).into() * 2)  // O Return the functor
}
```

### Scenario 3: Comonadic Contexts

```rust
// BEFORE
use rustica::datatypes::id::Id;
use rustica::traits::identity::Identity;

fn extract_value(id: &Id<i32>) -> i32 {
    *id.value()  // ❌ Deprecated
}

// AFTER
use rustica::datatypes::id::Id;
use rustica::traits::comonad::Comonad;

fn extract_value(id: &Id<i32>) -> i32 {
    id.extract()  // O Comonad (proper categorical semantics)
}
```

---

## Compatibility Shim (Temporary)

If you need time to migrate, you can temporarily allow deprecated warnings:

```rust
#![allow(deprecated)]

// Your existing code using Identity will still compile
// but you'll want to migrate eventually
```

---

## Benefits of This Change

O **Correct Category Theory**: Functor no longer requires value extraction  
O **Unified API**: All types use `unwrap()` for value extraction  
O **Simpler Code**: Use standard Rust methods instead of custom traits  
O **Less Confusion**: "Identity" no longer conflicts with identity functor  
O **Better Separation**: Comonad handles total extraction, `unwrap()` handles partial  
O **Vec Semantics**: `Vec<T>` no longer needs arbitrary `first()` implementation  
O **Consistent Learning**: One method name to learn for all value extraction  

---

## Timeline

- **v0.11.0**: `Identity` deprecated, `Functor: Identity` removed, **All types unified to `unwrap()`**
- **v0.12.0**: `Identity` trait will be completely removed
- **Migration period**: 1-2 major versions

---

## Need Help?

If you encounter issues during migration:

1. Check if you actually need value extraction (most Functor operations don't)
2. Use standard methods: `unwrap()`, `as_ref()`, `expect("message")`
3. For comonads: Use `Comonad::extract()`
4. Open an issue if you have a valid use case that's not covered

---

## Summary Table

|   Old (v0.10.x)    |    New (v0.11.0)    |           Reason             |
|--------------------|---------------------|------------------------------|
| `Functor: Identity`| `Functor: HKT`      | Category theory correctness  |
| `value()`          | `unwrap()`          | Standard Rust method         |
| `try_value()`      | `as_ref()`          | Standard Rust method         |
| `into_value()`     | `unwrap()`          | Standard Rust method         |
| `try_into_value()` | `Some(x)` or `self` | Not needed                   |
| `id.value()`       | `id.extract()`      | Comonad for total extraction |

### Value Extraction Methods by Type

|      Type      |      Standard Methods     |       Safe Methods      |     Comonad     |
|----------------|---------------------------|-------------------------|-----------------|
| `Option<T>`    | `unwrap()`, `unwrap_or()` | `as_ref()`, `ok_or()`   | N/A             |
| `Result<T, E>` | `unwrap()`, `unwrap_or()` | `as_ref()`, `map_err()` | N/A             |
| `Maybe<T>`     | `unwrap()`, `unwrap_or()` | `as_option()`           | N/A             |
| `Choice<T>`    | `unwrap()`, `unwrap_or()` | `first()`               | N/A             |
| `Either<L, R>` | `unwrap()`, `unwrap_or()` | `right()`, `left()`     | N/A             |
| `Id<T>`        | `unwrap()`                | N/A                     | `extract()`     |
| `Wrapper<T>`   | `unwrap()`                | N/A                     | N/A             |

**Guideline**: Use `unwrap()` for all value extraction across all types, `unwrap_or()` for safe defaults, and `Comonad::extract()` only for types with guaranteed total extraction.

---

## Key Takeaway: One Method to Rule Them All

**v0.11.0 unifies all value extraction to `unwrap()`** - whether you're working with `Option`, `Maybe`, `Choice`, `Either`, or any other Rustica type, `unwrap()` is your go-to method for value extraction.

**This is a breaking change, but it makes Rustica more correct, consistent, and easier to use.**
