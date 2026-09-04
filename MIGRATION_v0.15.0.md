# Rustica 0.15.0 Migration Guide

This guide describes the breaking changes and migration steps for Rustica 0.15.0.

## Summary of Changes

| API | Migration |
| --- | --- |
| `IsoLens<S, A, I>` | Removed; use `Lens::from_iso(iso)`. |
| `IsoPrism<S, A, I>` | Removed; use `Prism::from_iso(iso)`. |
| `Lens::compose(other)` | Use `Lens::then(other)`. |
| `Prism::compose(other)` | Use `Prism::then(other)`. |
| `pipeline_option` / `pipeline_result` | Use `Iterator::try_fold`. |
| `transform_chain(value, f)` | Use `Option::map` together with `Functor::fmap`. |
| `rustica::utils` / `rustica::prelude::utils` | Use standard iterator, `Option`, and `Result` operations. |
| `MonadPlus` | Removed; use `Alternative` (`empty_alt()` and `alt()`). |
| `ErrorMapper` | Removed; use `Result::map_err` or `Option::ok_or`. |
| `Applicative::ap2` | Removed; use `Applicative::lift2`. |
| `Sum`, `Product`, `Min`, `Max` (`unwrap`, `unwrap_or`) | Deprecated in 0.15.0; use `into_inner()` or `get()`. |
| `Product<T>: Monoid` | Bound updated from `From<u8>` to `rustica::traits::one::One`. |
| `Validated<E, A>: Semigroup` | Now requires `A: Semigroup` and accumulates `Valid` elements. |
| `Validated<E, A>: Alternative` | Omitted; `Validated` cannot lawfully implement `Alternative` (lacks empty identity for `NonEmptyErrors`). |
| `Choice::flatten` | Returns `Option<Choice<I>>` instead of panicking on empty iterators. |
| `StateT` / `ReaderT` (`*_with` combinators) | Removed manual closure threading methods. |
| `FunctionCategory::lift` | Removed; use `FunctionCategory::arrow`. |
| `Id::unwrap_or` | Removed; use `Id::into_inner` or `Id::unwrap`. |

## Optics

`Iso` values can now be lifted directly into the core optics:

```rust
use rustica::datatypes::{lens::Lens, prism::Prism};
use rustica::traits::iso::Iso;

#[derive(Clone, Copy)]
struct IdentityIso;

impl Iso<i32, i32> for IdentityIso {
    type From = i32;
    type To = i32;

    fn forward(&self, value: &i32) -> i32 {
        *value
    }

    fn backward(&self, value: &i32) -> i32 {
        *value
    }
}

let lens = Lens::from_iso(IdentityIso);
assert_eq!(lens.get(&42), 42);

let prism = Prism::from_iso(IdentityIso);
assert_eq!(prism.preview(&42), Some(42));
```

`Prism::from_iso` is for a total `Iso<S, A>` and always previews
successfully. The removed `IsoPrism` used an option-valued iso instead; migrate
it with `Prism::from_option_iso`, which preserves unmatched cases as `None`:

```rust
struct CaseIso;

impl Iso<MyEnum, Option<i32>> for CaseIso {
    type From = MyEnum;
    type To = Option<i32>;

    fn forward(&self, value: &MyEnum) -> Option<i32> {
        match value {
            MyEnum::Value(number) => Some(*number),
            MyEnum::Other => None,
        }
    }

    fn backward(&self, value: &Option<i32>) -> MyEnum {
        value.map_or(MyEnum::Other, MyEnum::Value)
    }
}

let prism = Prism::from_option_iso(CaseIso);
```

`IsoLens` and `IsoPrism` are removed in 0.15.0. Use `Lens::from_iso` for
ordinary isomorphisms and `Prism::from_option_iso` for the former
option-valued `IsoPrism` contract.

Use `then` for left-to-right optic composition:

```rust
let composed = first_lens.then(second_lens);
```

In categorical notation, `a.then(b)` corresponds to `b ∘ a`.

## FunctionCategory and Id API cleanup

`FunctionCategory::lift` was a forwarding alias for `FunctionCategory::arrow` and
has been removed. Construct function morphisms with `arrow`:

```rust
use rustica::category::function_category::FunctionCategory;

let doubled = FunctionCategory::arrow(|value: i32| value * 2);
assert_eq!(doubled(21), 42);
```

`Id` always contains a value, so `Id::unwrap_or` has been removed. Use
`into_inner()` to consume the wrapper or `unwrap()` when retaining the existing
terminology:

```rust
use rustica::datatypes::id::Id;

assert_eq!(Id::new(42).into_inner(), 42);
assert_eq!(Id::new(42).unwrap(), 42);
```

## Predicate

`Predicate` is exported from `rustica::prelude::*` and
`rustica::prelude::wrapper::*`. Its closure is now stored in an `Arc` and must
be `Send + Sync`:

```rust
use rustica::prelude::*;

let positive = Predicate::new(|value: &i32| *value > 0);
assert!(positive.contains(&1));
```

Predicates that capture non-thread-safe values must use thread-safe captures,
such as `Arc<Mutex<_>>`.

## IO

Combinators (`fmap`, `bind`, `apply`) on pure inputs now always return the
`Effect` representation; `is_pure()` reflects the representation, not evaluation cost.

`IO::run_async` now rethrows the original panic payload from the blocking
operation instead of replacing it with a generic join error message. No source
migration is required.

## Standard-library Replacements

For fallible operation pipelines, use `try_fold` directly:

```rust
fn add_one(value: i32) -> Result<i32, &'static str> {
    Ok(value + 1)
}

fn double(value: i32) -> Result<i32, &'static str> {
    Ok(value * 2)
}

let result = [
    add_one as fn(i32) -> Result<i32, &'static str>,
    double,
]
.into_iter()
.try_fold(5, |value, operation| operation(value));

assert_eq!(result, Ok(12));
```

## Algebraic Traits & Laws

### MonadPlus Deprecated and Removed

`MonadPlus` identically duplicated the choice and identity semantics of `Alternative`. The trait and module have been removed.

**Before (0.14.0):**

```rust
use rustica::traits::monad_plus::MonadPlus;

let opt = Option::<i32>::mzero();
let combined = Option::<i32>::mplus(&Some(1), &Some(2));
```

**After (0.15.0):**

```rust
use rustica::traits::alternative::Alternative;

let opt = Option::<i32>::empty_alt();
let combined = Some(1).alt(&Some(2));
```

### ErrorMapper Removed

`ErrorMapper` was a hollow trait forwarding to `Result::map_err`. Use standard library methods directly:

**Before (0.14.0):**

```rust
use rustica::traits::monad_error::ErrorMapper;

let result: Result<i32, &str> = Err("404");
let mapped = result.map_error_to(|e| format!("Code: {e}"));
```

**After (0.15.0):**

```rust
let result: Result<i32, &str> = Err("404");
let mapped = result.map_err(|e| format!("Code: {e}"));
```

### Applicative `ap2` Removed

`Applicative::ap2` was a redundant forwarding alias for `lift2`. Use `lift2` directly:

```rust
use rustica::traits::applicative::Applicative;

let result = Option::lift2(|a, b| a + b, &Some(2), &Some(3));
```

## Datatype Invariants

### Validated Semigroup Accumulation

In previous versions, `Validated<E, A>::combine` did not accumulate `Valid` components when both operands were valid. In 0.15.0:

`Semigroup for Validated<E, A>` requires `A: Semigroup`. When both operands are `Valid(a1)` and `Valid(a2)`, it returns `Valid(a1.combine(&a2))`. Any `Invalid` accumulates errors. Note that `Alternative for Validated<E, A>` is not implemented because `NonEmptyErrors<E>` contains at least 1 error and therefore lacks a lawful empty identity element for `empty_alt()`.

```rust
use rustica::datatypes::validated::Validated;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::traits::semigroup::Semigroup;

// Semigroup accumulates both errors and valid monoidal values:
let v1: Validated<String, Sum<i32>> = Validated::valid(Sum(10));
let v2: Validated<String, Sum<i32>> = Validated::valid(Sum(20));
assert_eq!(v1.combine(&v2), Validated::valid(Sum(30)));
```

### Product Monoid Bound (`One` Trait)

`Product<T>: Monoid` previously required `T: From<u8>`, which failed for signed types such as `i8` where `From<u8>` is intentionally not implemented in Rust. `rustica::traits::one::One` is now used:

```rust
use rustica::datatypes::wrapper::product::Product;
use rustica::traits::monoid::Monoid;

let id: Product<i8> = Product::empty();
assert_eq!(*id.get(), 1i8);
```

### Choice Flattening Safety

`Choice::flatten` previously panicked when called on an empty iterator. It now returns `Option<Choice<I>>`:

```rust
use rustica::datatypes::choice::Choice;

let choices = Choice::single(Vec::<i32>::new());
assert_eq!(choices.flatten(), None);
```

### Wrapper Types Accessors

The `.unwrap()` and `.unwrap_or()` methods on `Sum`, `Product`, `Min`, and `Max` are deprecated in 0.15.0 and superseded by standard accessors:

- `into_inner(self) -> T`: moves the inner value out of the wrapper without requiring `T: Clone`.
- `get(&self) -> &T`: borrows the inner value.
- `.0`: direct field access on the `pub T` tuple struct.

```rust
use rustica::datatypes::wrapper::sum::Sum;

let sum = Sum(42);
// Consume and extract:
assert_eq!(sum.into_inner(), 42);

let sum2 = Sum(10);
// Borrow:
assert_eq!(*sum2.get(), 10);
// Or access tuple field directly:
assert_eq!(sum2.0, 10);
```

## Transformers

### StateT and ReaderT Manual Combinators

The manual `*_with` forwarding combinators (`fmap_with`, `bind_with`, `combine_with`, `apply_with`) have been removed in favor of standard trait implementations. `ReaderT::lift2` is now an associated function:

```rust
use rustica::transformers::reader_t::ReaderT;

let lift = ReaderT::<(), Option<i32>, i32>::lift2(|a, b| a + b, |left, right, f| {
    left.and_then(|x| right.map(|y| f(x, y)))
});
```
