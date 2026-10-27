# Rustica 0.21.0 Migration Guide

Breaking API changes and direct replacement patterns for Rustica 0.21.0.

---

## Quick Reference

| Item | Status | Replacement |
| --- | --- | --- |
| `Validated::recover_all_at_once` callback input | Breaking (API) | Accept `NonEmptyErrors<E>` instead of `Vec<E>` |
| `ContextError::context` | Removed | `to_contexts()` |
| `ContextError::contexts_raw` | Removed | `contexts()` |
| `Lens::get` | Removed | `view(&s)` for a borrow or `to_value(&s)` for an owned clone |
| `Validated::recover_all` | Removed | `recover_all_at_once` or `recover_with`; use `map_err` to transform errors individually |
| `Lens::modify`, `Prism::modify` callback input | Breaking (API) | Accept `&A` instead of `A` in transformation closure `FnOnce(&A) -> A` |
| `Validated::collect` parameter | Non-breaking | Generalized from `Iterator` to `IntoIterator` |
| `NonEmptyErrors::iter`, `iter_mut` | Minor (Paths) | Inherent methods removed; `DerefMut<Target = [E]>` added; method calls unchanged |
| `free::ContFn<F>` | Made private | Define a local alias using `Arc<dyn Fn(AnyValue) -> Free<F, AnyValue> + Send + Sync + 'static>` if needed |
| `Validated::lift2`, `lift3` | Deprecated | Method syntax `v1.zip_with(v2, f)`, `v1.zip_with3(v2, v3, f)` |
| `Free::lift2` | Deprecated | Method syntax `fa.zip_with(fb, f)` |
| `operational::suspend`, `try_suspend` | Deprecated | `Command::suspend` / `Command::try_suspend`, or `Program::suspend` / `TryProgram::suspend` |
| `ContextError::context_iter` | Deprecated | `err.contexts().iter()` |
| `Validated::collect`, `Validated::sequence` | Deprecated | `iter.into_iter().collect::<Validated<C, E>>()`; `values.into_iter().collect::<Validated<Vec<_>, _>>().map(f)` |
| `Prism::set_with`, `Prism::modify_with` | Deprecated | Focus the whole variant payload; `set_always` / `modify_always` (or `set` / `modify`) |
| `Choice::flatten` | Deprecated | `try_flatten().ok()`, or `try_flatten()` to keep `ChoiceError` |
| `error::context_fn` | Deprecated | `with_context(e, c)` or `ContextError::new(e).with_context(c)` |
| `datatypes::error` module | Deprecated | `rustica::datatypes::{ChoiceError, FreeError}` or `rustica::prelude::*` |

## `Validated::recover_all_at_once` Callback Type

The callback now receives `NonEmptyErrors<E>`: an invalid `Validated` always holds at least one error. Closures that infer the argument type still compile. Closures that name `Vec<E>` must change:

```rust,ignore
// Before (0.20.0)
invalid.recover_all_at_once(|errors: Vec<String>| {
    Validated::invalid_many(errors)
});

// After (0.21.0)
use rustica::datatypes::validated::NonEmptyErrors;

invalid.recover_all_at_once(|errors: NonEmptyErrors<String>| {
    Validated::invalid_many(errors)
});
```

`NonEmptyErrors<E>` supports slice-style inspection and iteration. Use `into_vec()` only when an owned `Vec<E>` is required.

## Optics `modify` and `modify_always` Closure Signatures

Transformation closures in `Lens::modify`, `Lens::modify_always`, `Prism::modify`, `Prism::modify_always`, and `Prism::modify_with` now receive `&A` instead of `A` (`FnOnce(&A) -> A`). This avoids cloning the focus before the closure runs.

`Copy` types and reference operators such as `&i32 + i32` compile unchanged (`|x| x + 1`). When the closure needs an owned value or mutation, call `.clone()` explicitly:

```rust,ignore
// Before (0.20.0)
let updated = name_lens.modify(person, |mut name| {
    name.push_str(" Smith");
    name
});

// After (0.21.0)
let updated = name_lens.modify(person, |name| {
    let mut new_name = name.clone();
    new_name.push_str(" Smith");
    new_name
});
```

## `NonEmptyErrors` DerefMut and Method Call Compatibility

`NonEmptyErrors<E>` implements `core::ops::DerefMut<Target = [E]>` alongside `Deref`. The inherent `iter(&self)` and `iter_mut(&mut self)` methods were removed in favor of slice deref.

Method calls (`errors.iter()`, `errors.iter_mut()`) still resolve through deref coercion. Path calls such as `NonEmptyErrors::iter(&errors)` must change to `errors.as_slice().iter()` or `errors.iter()`.

## Removed Deprecated APIs

The deprecated compatibility methods were removed in 0.21.0. `Lens::view` borrows the focused value without cloning; `Lens::to_value` returns an owned clone. `ContextError::to_contexts` clones the context list; `contexts` borrows it.

`Validated::recover_all` has no direct replacement. It stopped at the first successful recovery and discarded the remaining errors. Use `recover_all_at_once` to decide on the complete error collection, `recover_with` for a fixed fallback, or `map_err` to transform each error while keeping the invalid result.
