# Migration Guide: v0.11.0

## Breaking Changes: Identity Trait Removal & Unify to unwrap()

### Overview

Version 0.11.0 removes the incorrect `Functor: Identity` dependency and deprecates the `Identity` trait entirely. This is a **breaking change** that aligns Rustica with proper category theory principles **and unifies all value extraction to standard `unwrap()` methods**.

**Complete Working Example**: See `examples/identity_migration_v0_11_0.rs` for a comprehensive, runnable demonstration of all Identity trait migration patterns with detailed explanations and test cases.

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
let value = choice.first().expect("Choice is empty"); // &T (panics if empty)
let safe = choice.first().unwrap_or(&0);              // &T with default
let first = choice.first();                           // Option<&T>

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

|      Type      |         Standard Methods      |       Safe Methods      |     Comonad     |
|----------------|-------------------------------|-------------------------|-----------------|
| `Option<T>`    | `unwrap()`, `unwrap_or()`     | `as_ref()`, `ok_or()`   | N/A             |
| `Result<T, E>` | `unwrap()`, `unwrap_or()`     | `as_ref()`, `map_err()` | N/A             |
| `Maybe<T>`     | `unwrap()`, `unwrap_or()`     | `as_option()`           | N/A             |
| `Choice<T>`    | `first().expect()`, `first()` | `first()`, `iter()`     | N/A             |
| `Either<L, R>` | `unwrap()`, `unwrap_or()`     | `right()`, `left()`     | N/A             |
| `Id<T>`        | `unwrap()`                    | N/A                     | `extract()`     |
| `Wrapper<T>`   | `unwrap()`                    | N/A                     | N/A             |

**Guideline**: Use `unwrap()` for all value extraction across all types, `unwrap_or()` for safe defaults, and `Comonad::extract()` only for types with guaranteed total extraction.

---

## Identity Migration Quick Reference

| Task | Before (Deprecated) | After (Recommended) |
|------|---------------------|-------------------|
| Extract value (Maybe) | `maybe.value()` | `maybe.unwrap()` |
| Extract value (Choice) | `choice.value()` | `choice.first().expect()` |
| Safe extraction | `maybe.try_value()` | `maybe.unwrap_or(default)` |
| Reference access | `maybe.try_value()` | `maybe.as_ref()` |
| Total extraction | `id.value()` | `id.extract()` |
| Consume into value | `maybe.into_value()` | `maybe.into_inner()` or `maybe.unwrap()` |

**Get Started**: Run the complete example:

```bash
cargo run --example identity_migration_v0_11_0
```

---

## Identity Migration Best Practices

### Pattern 1: Use unwrap() when you're confident

```rust
let config = Maybe::Just("production");
let env = config.unwrap(); // We know config is set
```

### Pattern 2: Use unwrap_or() for safe defaults

```rust
let user_setting = Maybe::<String>::Nothing;
let timeout = user_setting.unwrap_or("30s".to_string());
```

### Pattern 3: Use as_ref() when preserving the original

```rust
let cache = Maybe::Just("redis://localhost");
if let Some(cache_url) = cache.as_ref() {
    println!("Using cache: {}", cache_url);
    // cache is still available for later use
}
```

### Pattern 4: Use Comonad::extract() for algebraic types

```rust
use rustica::traits::comonad::Comonad;

let computation = Id::new(42 * 2);
let result = computation.extract(); // Total extraction (always succeeds)
```

### Pattern 5: Match for exhaustive handling

```rust
let either: Either<&str, i32> = Either::Left("error occurred");
match either {
    Either::Right(value) => println!("Success: {}", value),
    Either::Left(error) => println!("Error: {}", error),
}
```

### Pattern 6: Choice uses first() for primary value

```rust
let choice = Choice::new(42, vec![84, 126]);

// Get primary value (panics if empty)
let value = choice.first().expect("Choice has a primary value");

// Safe extraction with default
let safe = choice.first().unwrap_or(&0);

// Check if empty first
if let Some(primary) = choice.first() {
    println!("Primary: {}", primary);
}
```

### Pattern 7: Use iter() for flexible traversal

```rust
let choice = Choice::new(1, vec![2, 3, 4]);

// Get first value through iteration
let first = choice.iter().next();

// Process all values
for value in choice.iter() {
    println!("Value: {}", value);
}
```

---

## Breaking Changes: `Choice<T>` Utility Methods Deprecation

### `Choice<T>` Deprecation Overview

Version 0.11.0 deprecates numerous utility methods in `Choice<T>` that are not core categorical operations. This is a **breaking change** that simplifies the `Choice<T>` API to focus on essential Functor/Applicative/Monad/MonadPlus operations. All deprecated methods will be removed in v0.12.0.

**Complete Working Example**: See `examples/choice_migration_v0_11_0.rs` for a comprehensive, runnable demonstration of all migration patterns with detailed explanations and test cases.

---

## `Choice<T>` Changes

### Deprecated Methods (17 total)

The following methods are now deprecated and will be removed in v0.12.0:

#### Convenience/Redundant Methods

```rust
choice.has_alternatives()           // ❌ Deprecated
choice.to_vec()                     // ❌ Deprecated  
choice.find_first(predicate)        // ❌ Deprecated
choice.iter_alternatives()          // ❌ Deprecated
```

#### Non-Categorical Operations

```rust
choice.dedup()                      // ❌ Deprecated
choice.dedup_by_key(key_fn)         // ❌ Deprecated
choice.fold(initial, f)             // ❌ Deprecated
choice.to_map_with_key(key_fn)      // ❌ Deprecated
choice.add_alternatives(iter)       // ❌ Deprecated
choice.remove_alternative(index)    // ❌ Deprecated
choice.try_remove_alternative(index)// ❌ Deprecated
choice.swap_with_alternative(index) // ❌ Deprecated
choice.try_swap_with_alternative(index) // ❌ Deprecated
```

#### Semantically Confusing/Overly Specialized

```rust
choice.filter(predicate)            // ❌ Deprecated
choice.fmap_alternatives(f)         // ❌ Deprecated
choice.flatten_sorted()             // ❌ Deprecated
choice.bind_lazy(f)                 // ❌ Deprecated
```

### Retained Core Operations

These methods remain and are considered core categorical operations:

```rust
// Creation and basic access
Choice::new(primary, alternatives)  // Core
Choice::new_empty()                 // Core
Choice::of_many(iter)               // Core
choice.first()                      // Core
choice.alternatives()               // Core
choice.len()                        // Core
choice.is_empty()                   // Core

// Core categorical operations
choice.filter_values(predicate)     // Core (clear semantics)
choice.flatten()                    // Core (monadic)
choice.try_flatten()                // Core (safe)
choice.iter()                       // Core (iteration)

// All trait implementations (Functor, Applicative, Monad, MonadPlus, etc.)
choice.fmap(f)                      // Core (Functor)
choice.apply(other)                 // Core (Applicative)
choice.bind(f)                      // Core (Monad)
choice.combine(other)               // Core (Semigroup)
// ... and all other trait methods
```

---

## Rationale for Deprecation

### 1. Categorical Clarity

`Choice<T>` represents nondeterministic computation in category theory. The deprecated methods dilute this focus:

```rust
// BEFORE: Mixed concerns
choice.dedup()              // ❌ Collection utility
choice.flatten_sorted()     // ❌ Mixing categorical + ordering
choice.swap_with_alternative(0) // ❌ Index-based manipulation

// AFTER: Pure categorical operations
choice.filter_values(|x| x > 0)  // Clear filtering semantics
choice.flatten()                 // Pure monadic operation
choice.bind(f)                   // Pure monadic binding
```

### 2. API Surface Reduction

Too many utility methods made the API overwhelming and hid the core categorical purpose:

```rust
// BEFORE: 25+ methods - hard to know which are "core"
choice.has_alternatives()
choice.to_vec()
choice.find_first()
choice.dedup()
choice.dedup_by_key()
choice.fold()
choice.to_map_with_key()
// ... 20 more methods

// AFTER: 11 core methods + trait implementations
choice.first()
choice.alternatives()
choice.filter_values()
choice.flatten()
// ... plus standard categorical traits
```

### 3. Functional Programming Principles

Some methods violated FP principles:

```rust
// ❌ flatten_sorted() mixes categorical operation with ordering
// This breaks the principle that categorical operations should be order-agnostic
let sorted = choice.flatten_sorted();

// Separate concerns: categorical operation then external ordering
let flattened = choice.flatten();
let mut sorted_vec: Vec<_> = flattened.into_iter().collect();
sorted_vec.sort();
let sorted = Choice::from_iter(sorted_vec);
```

---

## Step-by-Step Migration

### Step 1: Replace Convenience Methods

```rust
// BEFORE
use rustica::datatypes::choice::Choice;

let choice = Choice::new(1, vec![2, 3]);

// Check for alternatives
if choice.has_alternatives() {  // ❌ Deprecated
    println!("Has alternatives");
}

// Convert to Vec
let vec = choice.to_vec();      // ❌ Deprecated

// Find first matching
let found = choice.find_first(|&x| x > 2);  // ❌ Deprecated

// Iterate alternatives
for alt in choice.iter_alternatives() {  // ❌ Deprecated
    println!("Alt: {}", alt);
}

// AFTER
use rustica::datatypes::choice::Choice;

let choice = Choice::new(1, vec![2, 3]);

// Check for alternatives
if !choice.alternatives().is_empty() {  // Clear semantics
    println!("Has alternatives");
}

// Convert to Vec
let vec = choice.into_iter().cloned().collect();  // Standard pattern
// OR: let vec = Into::<Vec<i32>>::into(choice);

// Find first matching
let found = choice.iter().find(|&x| x > 2);  // Standard iterator

// Iterate alternatives
for alt in choice.alternatives().iter() {  // Direct slice access
    println!("Alt: {}", alt);
}
```

### Step 2: Replace Non-Categorical Operations

```rust
// BEFORE
let choice = Choice::new(1, vec![2, 3, 2, 4]);

// Deduplication
let unique = choice.dedup();                    // ❌ Deprecated
let unique_by_key = choice.dedup_by_key(|x| x % 2); // ❌ Deprecated

// Folding
let sum = choice.fold(0, |acc, &x| acc + x);    // ❌ Deprecated

// Map conversion
let map = choice.to_map_with_key(|x| x % 2);    // ❌ Deprecated

// Adding alternatives
let expanded = choice.add_alternatives(vec![5, 6]); // ❌ Deprecated

// AFTER
use rustica::traits::foldable::Foldable;
use std::collections::HashMap;

let choice = Choice::new(1, vec![2, 3, 2, 4]);

// Deduplication - external iteration (preserves order)
let unique: Choice<i32> = {
    let mut seen = std::collections::HashSet::new();
    choice.iter()
        .filter(|x| seen.insert(*x))  // Keep first occurrence
        .cloned()
        .collect()
};

let unique_by_key: Choice<i32> = {
    let mut seen = std::collections::HashSet::new();
    choice.iter()
        .filter(|&x| seen.insert(x % 2))  // Keep first per key
        .cloned()
        .collect()
};

// Folding - use Foldable trait
let sum = choice.fold_left(0, |acc, &x| acc + x);  // Categorical

// Map conversion - keep first value per key
let map: HashMap<i32, i32> = choice.iter()
    .fold(HashMap::new(), |mut acc, &x| {
        acc.entry(x % 2).or_insert(x);  // Keep first
        acc
    });

// Adding alternatives - use Semigroup
use rustica::traits::semigroup::Semigroup;
let expanded = choice.combine(&Choice::new(5, vec![6])); // Categorical
```

### Step 3: Replace Index-Based Operations

```rust
// BEFORE
let choice = Choice::new(1, vec![2, 3, 4]);

// Remove by index
let removed = choice.remove_alternative(1);  // ❌ Deprecated
let safe_removed = choice.try_remove_alternative(1); // ❌ Deprecated

// Swap with alternative
let swapped = choice.swap_with_alternative(0);  // ❌ Deprecated
let safe_swapped = choice.try_swap_with_alternative(0); // ❌ Deprecated

// AFTER
let choice = Choice::new(1, vec![2, 3, 4]);

// Remove by condition
let removed = choice.filter_values(|&x| x != 3);  // Clear semantics

// For more complex removal logic, use external iteration
let filtered: Choice<i32> = choice.iter()
    .enumerate()
    .filter(|(i, _)| *i != 2) // Skip index 2 (value 3)
    .map(|(_, &x)| x)
    .collect();

// Swapping - use external patterns or restructure
// If you need to promote an alternative to primary:
let choice2 = Choice::new(3, vec![1, 2, 4]); // Explicit construction
```

### Step 4: Replace Semantically Confusing Methods

```rust
// BEFORE
let choice = Choice::new(1, vec![2, 3, 4]);

// Filter alternatives only (preserves primary unconditionally)
let filtered = choice.filter(|&x| x > 2);  // ❌ Deprecated - unclear semantics

// Map alternatives only
let mapped = choice.fmap_alternatives(|x| x * 2);  // ❌ Deprecated

// Flatten with sorting
let sorted_flat = choice.flatten_sorted();  // ❌ Deprecated - mixed concerns

// Lazy bind
let lazy_iter = choice.bind_lazy(|x| Choice::new(x * 2, vec![x * 3])); // ❌ Deprecated

// AFTER
let choice = Choice::new(1, vec![2, 3, 4]);

// Filter all values (may change primary)
let filtered = choice.filter_values(|&x| x > 2);  // Clear semantics

// Map all values with conditional logic
let mapped = choice.fmap(|x| if x > 1 { x * 2 } else { x });  // Flexible

// Separate categorical and ordering concerns
let flattened = choice.flatten();  // Pure categorical
let sorted_flat: Choice<i32> = {
    let mut sorted_vec: Vec<_> = flattened.into_iter().collect();
    sorted_vec.sort();
    Choice::from_iter(sorted_vec)
}; // External

// Use standard bind with iteration
let eager: Choice<i32> = choice.bind(|x| Choice::new(x * 2, vec![x * 3])); // Standard
let lazy_iter = choice.iter().flat_map(|x| {
    let result = Choice::new(x * 2, vec![x * 3]);
    result.into_iter()
}); // External lazy pattern
```

---

## Common Migration Patterns

### Pattern 1: Collection Utilities

```rust
// BEFORE - using Choice as a collection
let choice = Choice::new(1, vec![2, 3, 4, 5]);
let even = choice.filter(|&x| x % 2 == 0);
let unique = choice.dedup();
let sum = choice.fold(0, |acc, &x| acc + x);

// AFTER - using Choice as a categorical structure
let choice = Choice::new(1, vec![2, 3, 4, 5]);
let even = choice.filter_values(|&x| x % 2 == 0);  // Clear filtering
let unique = {
    let mut seen = HashSet::new();
    choice.iter().filter(|&x| seen.insert(x)).cloned().collect()
};  // Order-preserving dedup
let sum = choice.fold_left(0, |acc, &x| acc + x);  // Categorical folding
```

### Pattern 2: Index-Based Manipulation

```rust
// BEFORE - index-based thinking
let choice = Choice::new(1, vec![2, 3, 4, 5]);
let without_third = choice.remove_alternative(2);
let with_swapped = choice.swap_with_alternative(0);

// AFTER - value-based thinking
let choice = Choice::new(1, vec![2, 3, 4, 5]);
let without_third = choice.filter_values(|&x| x != 4);  // Remove by value
let with_swapped = Choice::new(2, vec![1, 3, 4, 5]);   // Explicit construction
```

### Pattern 3: Mixed Operations

```rust
// BEFORE - mixing concerns
let choice = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
let result = choice.flatten_sorted();  // Mixes flatten + sort

// AFTER - separate concerns
let choice = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
let flattened = choice.flatten();  // Pure categorical
let result: Choice<i32> = {
    let mut sorted_vec: Vec<_> = flattened.into_iter().collect();
    sorted_vec.sort();
    Choice::from_iter(sorted_vec)
};  // External ordering
```

---

## Performance Considerations

### Before vs After

```rust
// BEFORE - optimized internal implementations
choice.dedup()              // O(n) with internal HashSet
choice.flatten_sorted()     // O(n log n) with internal sort

// AFTER - external patterns (preserves semantics correctly)
{ let mut s = HashSet::new(); choice.iter().filter(|&x| s.insert(x)).cloned().collect() }  // O(n), order-preserving
{
    let mut sorted_vec: Vec<_> = choice.flatten().into_iter().collect();
    sorted_vec.sort();
    Choice::from_iter(sorted_vec)
}  // O(n log n) but clearer
```

**Note**: The external patterns may have slightly more allocation overhead, but they provide:

- Clearer intent
- Standard Rust patterns
- Better composability
- Categorical purity

If performance is critical, you can implement custom optimized functions for your specific use case.

---

## Compatibility Shim (Temporary)

If you need time to migrate, you can temporarily allow deprecated warnings:

```rust
#![allow(deprecated)]

// Your existing code will still compile with warnings
// but you'll want to migrate before v0.12.0
```

## Advantages of Refactoring

**Categorical Clarity**: `Choice<T>` focuses on nondeterministic computation  
**Smaller API**: Easier to learn and use  
**FP Principles**: No mixing of categorical and utility operations  
**Standard Patterns**: Uses familiar Rust iterator patterns  
**Better Composability**: External patterns are more flexible  
**Clear Semantics**: Each method has a clear, unambiguous purpose  

---

## Migration Support

If you encounter issues during migration:

1. **Try the working example**: Run `cargo run --example choice_migration_v0_11_0` to see all patterns in action
2. **Identify your use case**: Are you using `Choice<T>` as a collection or categorical structure?
3. **Use standard patterns**: Iterator, `collect()`, `filter()`, `map()` are your friends
4. **Consider the semantics**: Does your operation make sense for nondeterministic computation?
5. **Run the tests**: Execute `cargo test --example choice_migration_v0_11_0` to verify your understanding
6. **Open an issue**: If you have a valid categorical use case that's not covered

---

## Deprecation Timeline

- **v0.11.0**: Utility methods deprecated (with warnings)
- **v0.12.0**: All deprecated methods will be **completely removed**
- **Migration period**: 1 major version

---

## Quick Reference

|         Task         |       Before (Deprecated)       |                         After (Recommended)                         |
|----------------------|---------------------------------|---------------------------------------------------------------------|
| Check alternatives   | `choice.has_alternatives()`     | `!choice.alternatives().is_empty()`                                 |
| Convert to Vec       | `choice.to_vec()`               | `choice.iter().cloned().collect()`                                  |
| Find first match     | `choice.find_first(pred)`       | `choice.iter().find(pred)`                                          |
| Iterate alternatives | `choice.iter_alternatives()`    | `choice.alternatives().iter()`                                      |
| Remove duplicates    | `choice.dedup()`                | `{ let mut s = HashSet::new(); choice.iter().filter(\|&x\| s.insert(x)).cloned().collect() }` |
| Fold/Reduce          | `choice.fold(init, f)`          | `choice.fold_left(&init, f)`                                        |
| Add alternatives     | `choice.add_alternatives(iter)` | `choice.combine(&other_choice)`                                     |
| Sort + flatten       | `choice.flatten_sorted()`       | `Choice::from_iter({ let mut v = choice.flatten().into_iter().collect::<Vec<_>>(); v.sort(); v })`      |

**Get Started**: Run the complete example:

```bash
cargo run --example choice_migration_v0_11_0
```

---

## Migration Summary Table

|        Deprecated Method      |             Replacement           |        Category        |          Reason          |
|-------------------------------|-----------------------------------|------------------------|--------------------------|
| `has_alternatives()`          | `!alternatives().is_empty()`      | Convenience            | Redundant                |
| `to_vec()`                    | `Into::<Vec<T>>::into()`          | Convenience            | Standard conversion      |
| `find_first()`                | `iter().find()`                   | Convenience            | Standard iterator        |
| `iter_alternatives()`         | `alternatives().iter()`           | Convenience            | Direct slice access      |
| `dedup()`                     | External iteration with `HashSet` | Non-categorical        | Collection utility       |
| `dedup_by_key()`              | External iteration with `HashMap` | Non-categorical        | Collection utility       |
| `fold()`                      | `Foldable::fold_left()`           | Non-categorical        | Use categorical trait    |
| `to_map_with_key()`           | `iter().map().collect()`          | Non-categorical        | Standard pattern         |
| `add_alternatives()`          | `Semigroup::combine()`            | Non-categorical        | Use categorical trait    |
| `remove_alternative()`        | `filter_values()`                 | Non-categorical        | Index-based manipulation |
| `try_remove_alternative()`    | `filter_values()`                 | Non-categorical        | Index-based manipulation |
| `swap_with_alternative()`     | External patterns                 | Non-categorical        | Index-based manipulation |
| `try_swap_with_alternative()` | External patterns                 | Non-categorical        | Index-based manipulation |
| `filter()`                    | `filter_values()`                 | Semantically confusing | Unclear semantics        |
| `fmap_alternatives()`         | `fmap()` with conditions          | Overly specialized     | Too specific             |
| `flatten_sorted()`            | `flatten()` + external sort       | FP violation           | Mixed concerns           |
| `bind_lazy()`                 | `bind()` + external iteration     | Overly specialized     | Too specific             |

---

## Key Takeaway: Focus on Categorical Core

**v0.11.0 refocuses `Choice<T>` on its categorical purpose** - representing nondeterministic computation with clear Functor/Applicative/Monad/MonadPlus semantics.

**Utility operations should use standard Rust patterns**, while `Choice<T>` provides the categorical structure and operations.

**This is a breaking change, but it makes `Choice<T>` more principled, easier to understand, and better aligned with functional programming theory.**

---

## Key Takeaway: One Method to Rule Them All

**v0.11.0 unifies all value extraction to `unwrap()`** - whether you're working with `Option`, `Maybe`, `Choice`, `Either`, or any other Rustica type, `unwrap()` is your go-to method for value extraction.

**This is a breaking change, but it makes Rustica more correct, consistent, and easier to use.**
