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

## Removed Deprecated APIs

The deprecated compatibility methods were removed in 0.21.0. `Lens::view` borrows
the focused value without cloning; `Lens::to_value` returns an owned clone.
`ContextError::to_contexts` clones the context list, while `contexts` borrows it.

`Validated::recover_all` had no equivalent replacement because it stopped at the
first successful recovery and discarded any remaining errors. Use
`recover_all_at_once` to decide based on the complete error collection,
`recover_with` for a fixed fallback, or `map_err` to transform each error while
preserving the invalid result.
