# Rustica 0.15.0 Migration Guide

This guide describes the unreleased changes planned for Rustica 0.15.0. The
crate remains version 0.14.0 until that release is published.

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

`IsoLens` and `IsoPrism` are removed in 0.15.0. Use `Lens::from_iso` and
`Prism::from_iso` instead.

Use `then` for left-to-right optic composition:

```rust
let composed = first_lens.then(second_lens);
```

In categorical notation, `a.then(b)` corresponds to `b ∘ a`.

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

## IO Panic Behavior

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
