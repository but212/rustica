# HKT Utils Changes Guide

## Overview

Version 0.11.0 consolidates the `map_result` function from `hkt_utils` into `categorical_utils`.

---

## What Changed

```rust
// OLD location (still works via re-export)
use rustica::utils::hkt_utils::map_result;

// NEW canonical location
use rustica::utils::categorical_utils::map_result;
```

### Backward Compatibility

`hkt_utils::map_result` now re-exports from `categorical_utils::map_result`, so existing code will continue to work without changes.

### Signature Change

```rust
// OLD (v0.10.x) - used Fn
fn map_result<T, U, E, F>(result: Result<T, E>, f: F) -> Result<U, E>
where
    F: Fn(T) -> U

// NEW (v0.11.0) - uses FnOnce (more flexible)
fn map_result<T, U, E, F>(result: Result<T, E>, f: F) -> Result<U, E>
where
    F: FnOnce(T) -> U
```

`FnOnce` is more permissive than `Fn`, so this change is backward compatible for most use cases.

---

## Migration

### No Changes Required (Most Cases)

If you import from `hkt_utils`, your code continues to work:

```rust
use rustica::utils::hkt_utils::map_result;

let result: Result<i32, &str> = Ok(42);
let mapped = map_result(result, |x| x * 2);
```

### Preferred Import (New Code)

For new code, prefer importing from `categorical_utils`:

```rust
use rustica::utils::categorical_utils::map_result;

let result: Result<i32, &str> = Ok(42);
let mapped = map_result(result, |x| x * 2);
```

### Using FnOnce Closures

The `FnOnce` signature allows closures that consume captured values:

```rust
use rustica::utils::categorical_utils::map_result;

let data = vec![1, 2, 3];
let result: Result<(), &str> = Ok(());

// This now works - closure consumes `data`
let mapped = map_result(result, |_| {
    let owned = data;  // Takes ownership
    owned.len()
});
```

---

## Summary

| Change | Impact |
|--------|--------|
| `map_result` moved to `categorical_utils` | Re-export maintains compatibility |
| Signature changed to `FnOnce` | More flexible, backward compatible |

No action required for existing code. Consider updating imports in new code for clarity.
