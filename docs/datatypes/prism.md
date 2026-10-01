# Prism (`Prism<S, A, PreviewFn, ReviewFn>`)

Optic for borrowed inspection and immutable updates of a sum type variant.

## Quick Start

```rust
use rustica::datatypes::prism::Prism;

#[derive(Debug, Clone, PartialEq)]
enum Status { Active(String), Inactive, Pending(u32) }

// Create prisms for enum variants
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

// Borrow references
assert_eq!(active_prism.preview(&active_user), Some(&"Alice".to_string()));
assert_eq!(active_prism.preview(&pending_user), None);
assert_eq!(pending_prism.preview(&pending_user), Some(&7));

// Extract owned values
assert_eq!(active_prism.to_value(&active_user), Some("Alice".to_string()));

// Construct variants
let new_active = active_prism.review("Bob".to_string());
assert_eq!(new_active, Status::Active("Bob".to_string()));

// Transform variants
let updated = pending_prism.modify(pending_user, |days| days + 1);
assert_eq!(updated, Status::Pending(8));
```

## Key Features

- **Borrowed Preview**: Borrows focus directly (`preview(&s) -> Option<&A>`).
- **Owned Extraction**: Clones focus per `C-CONV` (`to_value(&s) -> Option<A>`).
- **Bidirectional**: Constructs sum types from variant focus (`review(a) -> S`).
- **Short-Circuiting**: `set` and `modify` return `source` unchanged when values match under `PartialEq`.
- **Composable**: `then` chains prisms across nested sum types.

## Type Class Laws

Prisms satisfy Preview-Review and Review-Preview laws. See [`Prism`] documentation for definitions and invariants.
