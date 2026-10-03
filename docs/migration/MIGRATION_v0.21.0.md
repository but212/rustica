# Rustica 0.21.0 Migration Guide

Breaking API changes and direct replacement patterns for Rustica 0.21.0.

---

## Quick Reference

| Item | Status | Replacement |
| --- | --- | --- |
| `Validated::recover_all_at_once` callback input | Breaking (API) | Accept `NonEmptyErrors<E>` instead of `Vec<E>` |

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
