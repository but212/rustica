# Prism (`Prism<S, A, PreviewFn, ReviewFn>`)

Prisms are reference-borrowing optics that focus on a specific case of a sum type.

A prism provides a way to:

- Selectively view a specific variant of an enum with zero heap allocations (`preview(&s) -> Option<&A>`)
- Extract an owned value when needed adhering to `C-CONV` conventions (`to_value(&s) -> Option<A>`)
- Construct a value of the sum type from a value of the specific variant (`review(a) -> S`)
- Update the variant with zero-allocation short-circuiting on unchanged values (`set`, `modify`)

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

## Functional Programming Context

Prisms represent a fundamental optic in functional programming, originating from the Haskell lens library.
In Rustica 0.20.0, prisms are reference-first: `preview` borrows directly without cloning, eliminating
heap churn for read-only variant inspection and chaining.

## Key Features

- **Zero-Allocation Preview**: Primary accessor borrows focus directly (`&S -> Option<&A>`).
- **Zero-Allocation Short-Circuiting**: `set` and `modify` preserve `source` untouched when `A: PartialEq` and values match.
- **Bidirectional**: Symmetrically extracts variant focus and constructs sum types.
- **Composable**: Chaining via `then` preserves references across arbitrary optic depths without intermediate clones.

## Type Class Laws

Prisms must satisfy the Preview-Review and Review-Preview laws to be well-behaved.
See the type-level [`Prism`] documentation for full definitions and invariants.
