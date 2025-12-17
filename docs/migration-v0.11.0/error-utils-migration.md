# Error Utils Module Migration Guide

## Overview

Version 0.11.0 moves all error utilities from `utils::error_utils` to `crate::error` and removes legacy error types.

---

## Module Relocation

### What Changed

```rust
// OLD (v0.10.x)
use rustica::utils::error_utils::{WithError, ResultExt, sequence, traverse};

// NEW (v0.11.0)
use rustica::error::{WithError, ResultExt, sequence, traverse};
// OR via prelude
use rustica::prelude::error::*;
```

### Why

Consolidating error handling utilities into a dedicated `error` module provides:

- Better discoverability
- Clearer module organization
- Consistent import paths

---

## Legacy AppError Removal

### What Changed

```rust
// REMOVED in v0.11.0
use rustica::utils::error_utils::{AppError, error, error_with_context};
```

### Why

After a deprecation cycle, these legacy utilities have been removed. All error construction is now routed through `ComposableError`.

### Migration

```rust
// OLD (v0.10.x)
use rustica::utils::error_utils::{AppError, error, error_with_context};

let err = error("Something went wrong");
let err_ctx = error_with_context("Failed", "in user validation");

// NEW (v0.11.0)
use rustica::error::ComposableError;

let err = ComposableError::new("Something went wrong");
let err_ctx = ComposableError::new("Failed")
    .with_context("in user validation");
```

---

## ComposableError API

```rust
use rustica::error::ComposableError;

// Creation
let err = ComposableError::new("base error message");

// Adding context (O(1) operation)
let err = err.with_context("additional context");

// Chaining multiple contexts
let err = ComposableError::new("database error")
    .with_context("while saving user")
    .with_context("in registration flow");

// Accessing context
for ctx in err.context_iter() {
    println!("Context: {}", ctx);
}

// Formatting
println!("{}", err);  // Displays error with all context
```

---

## Migrated Utilities

All these utilities are now in `rustica::error`:

| Utility | Description |
|---------|-------------|
| `WithError` | Error context trait |
| `ResultExt` | Result extension methods |
| `sequence` | Sequence Results into Result of Vec |
| `traverse` | Traverse with fallible function |
| `ComposableError` | Context-accumulating error type |
| `ErrorContext` | Lightweight error context |
| `ErrorPipeline` | Functional error handling pipeline |

---

## Summary

| Change | Migration |
|--------|-----------|
| `utils::error_utils::*` moved | `use rustica::error::*` |
| `AppError` removed | Use `ComposableError::new()` |
| `error()` removed | Use `ComposableError::new()` |
| `error_with_context()` removed | Use `ComposableError::new().with_context()` |
