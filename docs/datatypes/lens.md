# Lens (`Lens<S, A, ViewFn, SetFn>`)

Optic for borrowed viewing and immutable updates of nested structures.

## Quick Start

```rust
use rustica::datatypes::lens::Lens;

#[derive(Clone, Debug, PartialEq)]
struct Person { name: String, age: u32 }

// Create lenses for struct fields
let name_lens = Lens::new(
    |p: &Person| &p.name,
    |p: Person, name: String| Person { name, ..p },
);
let age_lens = Lens::new(
    |p: &Person| &p.age,
    |p: Person, age: u32| Person { age, ..p },
);

let person = Person { name: "Alice".to_string(), age: 30 };

// Borrow references
assert_eq!(name_lens.view(&person), "Alice");
assert_eq!(*age_lens.view(&person), 30);

// Extract owned values
assert_eq!(name_lens.to_value(&person), "Alice");

// Set values immutably (short-circuits when unchanged)
let renamed = name_lens.set(person.clone(), "Bob".to_string());
assert_eq!(renamed, Person { name: "Bob".to_string(), age: 30 });

// Transform values
let older = age_lens.modify(person, |age| age + 1);
assert_eq!(older.age, 31);
```

## Key Features

- **Borrowed View**: Borrows focus directly (`view(&s) -> &A`).
- **Owned Extraction**: Clones focus per `C-CONV` (`to_value(&s) -> A`).
- **Short-Circuiting**: `set` and `modify` return `source` unchanged when values match under `PartialEq`.
- **Bidirectional**: Pairs field inspection with product updates.
- **Composable**: `then` chains lenses across nested structures.

## Type Class Laws

1. **GetSet**: `lens.set(s.clone(), lens.to_value(&s)) == s`
2. **SetGet**: `*lens.view(&lens.set(s, a)) == a` (under `PartialEq`; for bit-exact types like `f64` where `-0.0 == 0.0` or non-reflexive `NaN`, use `set_always`)
3. **SetSet**: `lens.set(lens.set(s, a1), a2) == lens.set(s, a2)`
