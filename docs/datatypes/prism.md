# Prism (`Prism<S, A, PreviewFn, ReviewFn>`)

Optic for zero-allocation viewing and immutably updating a specific variant of a sum type.

## Quick Start

```rust
use rustica::datatypes::prism::Prism;

#[derive(Debug, Clone, PartialEq)]
enum Status { Active(String), Inactive, Pending(u32) }

// Create reference-borrowing prisms for enum variants
let active_prism = Prism::new(
    |s: &Status| match s {
        Status::Active(name) => Some(name),
        _ => None,
    },
    Status::Active,
);

let pending_prism = Prism::new(
    |s: &Status| match s {
        Status::Pending(days) => Some(days),
        _ => None,
    },
    Status::Pending,
);

let active_user = Status::Active("Alice".to_string());
let pending_user = Status::Pending(7);

// Extract borrowed references with zero allocations
assert_eq!(active_prism.preview(&active_user), Some(&"Alice".to_string()));
assert_eq!(active_prism.preview(&pending_user), None);
assert_eq!(pending_prism.preview(&pending_user), Some(&7));

// Extract owned values adhering to C-CONV
assert_eq!(active_prism.to_value(&active_user), Some("Alice".to_string()));

// Construct enum variants
let new_active = active_prism.review("Bob".to_string());
assert_eq!(new_active, Status::Active("Bob".to_string()));

// Transform specific variants
let updated = pending_prism.modify(pending_user, |days| days + 1);
assert_eq!(updated, Status::Pending(8));
```

## Key Features

- **Zero-Allocation Preview**: Primary accessor borrows focus directly (`preview(&s) -> Option<&A>`).
- **Owned Extraction**: Extracts owned values adhering to `C-CONV` (`to_value(&s) -> Option<A>`).
- **Bidirectional**: Constructs sum types from variant focus (`review(a) -> S`).
- **Short-Circuiting**: `set` and `modify` preserve `source` untouched when `A: PartialEq` and values match.
- **Composable**: Chaining via `then` preserves references across arbitrary optic depths without intermediate clones.

## Type Class Laws

Prisms satisfy Preview-Review and Review-Preview laws. See the type-level [`Prism`] documentation for definitions and invariants.
