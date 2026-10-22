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
| `operational::suspend`, `try_suspend` | Deprecated | `Command::suspend` or `Program::suspend` / `TryProgram::suspend` |
| `ContextError::context_iter` | Deprecated | `err.contexts().iter()` |
| `Validated::collect`, `Validated::sequence` | Deprecated | `iter.into_iter().collect::<Validated<C, E>>()`; `values.into_iter().collect::<Validated<Vec<_>, _>>().map(f)` |
| `Prism::set_with`, `Prism::modify_with` | Deprecated | Focus the whole variant payload; `set_always` / `modify_always` (or `set` / `modify`) |
| `Choice::flatten` | Deprecated | `try_flatten().ok()`, or `try_flatten()` to keep `ChoiceError` |
| `error::context_fn` | Deprecated | `with_context(e, c)` or `ContextError::new(e).with_context(c)` |
| `datatypes::error` module | Deprecated | `rustica::datatypes::{ChoiceError, FreeError}` or `rustica::prelude::*` |

## `Validated::recover_all_at_once` Callback Type

The callback now receives `NonEmptyErrors<E>`, reflecting the invariant that an
invalid `Validated` always contains at least one error. Closures that infer the
argument type and use its collection methods continue to work. Update closures
that explicitly name `Vec<E>`:

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

`NonEmptyErrors<E>` supports slice-style inspection and iteration through its
public API. Convert it with `into_vec()` only when an owned `Vec<E>` is required.

## Optics `modify` and `modify_always` Closure Signatures

Transformation closures in `Lens::modify`, `Lens::modify_always`, `Prism::modify`, `Prism::modify_always`, and `Prism::modify_with` now receive a borrowed reference `&A` instead of an owned `A` (`FnOnce(&A) -> A`). This eliminates mandatory cloning of the focus prior to calling the closure, allowing zero-allocation inspection and comparison when the value is unmodified.

For primitive types that implement `Copy` or operations like `+` on references (`&i32 + i32`), existing code like `|x| x + 1` compiles without changes. When ownership or mutating operations on owned values are required, call `.clone()` explicitly within the closure:

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

`NonEmptyErrors<E>` implements `core::ops::DerefMut<Target = [E]>` alongside `Deref`. The inherent methods `iter(&self)` and `iter_mut(&mut self)` were removed in favor of slice deref operations.

Method call syntax (`errors.iter()` and `errors.iter_mut()`) continues to resolve seamlessly through deref coercion. Code that referenced the inherent function by path (`NonEmptyErrors::iter(&errors)`) should be updated to slice syntax or method call syntax (`errors.as_slice().iter()` or `errors.iter()`).

## Deprecated Monad and Combinator Helpers

Top-level combinators `lift2`, `lift3`, and free functions `operational::suspend` / `try_suspend` have been deprecated in favor of direct method syntax:

- Replace `Validated::lift2(f, v1, v2)` with `v1.zip_with(v2, f)`
- Replace `Validated::lift3(f, v1, v2, v3)` with `v1.zip_with3(v2, v3, f)`
- Replace `Free::lift2(f, fa, fb)` with `fa.zip_with(fb, f)`
- Replace `operational::suspend(cmd)` with `cmd.suspend()` or `Program::suspend(cmd)`
- Replace `operational::try_suspend(cmd)` with `cmd.try_suspend()` or `TryProgram::suspend(cmd)`

## Removed Deprecated APIs

The deprecated compatibility methods were removed in 0.21.0. `Lens::view` borrows
the focused value without cloning; `Lens::to_value` returns an owned clone.
`ContextError::to_contexts` clones the context list, while `contexts` borrows it.

`Validated::recover_all` had no equivalent replacement because it stopped at the
first successful recovery and discarded any remaining errors. Use
`recover_all_at_once` to decide based on the complete error collection,
`recover_with` for a fixed fallback, or `map_err` to transform each error while
preserving the invalid result.
