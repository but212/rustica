# Lens (`Lens<S, A, ViewFn, SetFn>`)

Lens is a functional programming optic for zero-allocation viewing and modifying parts of immutable data structures.

A lens provides a way to:

- View a part of a larger data structure with zero heap allocations (`view(&s) -> &A`)
- Extract an owned value adhering to `C-CONV` conventions (`to_value(&s) -> A`)
- Update that part immutably while preserving the rest of the structure (`set`, `modify`)
- Short-circuit updates when `A: PartialEq` and new value equals current value (0 B, 0 clones)

## Quick Start

```rust
use rustica::datatypes::lens::Lens;

#[derive(Clone, Debug, PartialEq)]
struct Person { name: String, age: u32 }

// Create reference-borrowing lenses for struct fields
let name_lens = Lens::new(
    |p: &Person| &p.name,
    |p: Person, name: String| Person { name, ..p },
);
let age_lens = Lens::new(
    |p: &Person| &p.age,
    |p: Person, age: u32| Person { age, ..p },
);

let person = Person { name: "Alice".to_string(), age: 30 };

// Borrow references with zero allocations
assert_eq!(name_lens.view(&person), "Alice");
assert_eq!(*age_lens.view(&person), 30);

// Extract owned values adhering to C-CONV
assert_eq!(name_lens.to_value(&person), "Alice");

// Set values immutably (short-circuits on unchanged value)
let renamed = name_lens.set(person.clone(), "Bob".to_string());
assert_eq!(renamed, Person { name: "Bob".to_string(), age: 30 });

// Transform values with modify
let older = age_lens.modify(person, |age| age + 1);
assert_eq!(older.age, 31);
```

## Functional Programming Context

In functional programming, lenses are a form of *functional reference* or *optic* that solve the
problem of updating immutable nested data structures. In Rustica 0.20.0, lenses are reference-first:
`view` borrows directly without cloning, eliminating heap churn for read-only field inspection and chaining.

## Key Features

- **Zero-Allocation View**: Primary accessor borrows focus directly (`&S -> &A`).
- **Zero-Allocation Short-Circuiting**: `set` and `modify` preserve `source` untouched when `A: PartialEq` and values match.
- **Bidirectional**: Symmetrically views fields and updates product types.
- **Composable**: Chaining via `then` preserves references across arbitrary optic depths.

## Type Class Laws

Lenses follow three fundamental laws:

1. **GetSet**: `lens.set(s.clone(), lens.to_value(&s)) == s`
2. **SetGet**: `*lens.view(&lens.set(s, a)) == a` (equality is `PartialEq`; for
   bit-exact types such as `f64` where `-0.0 == 0.0` or non-reflexive types such as `NaN`, prefer `set_always`, which never short-circuits)
3. **SetSet**: `lens.set(lens.set(s, a1), a2) == lens.set(s, a2)`
