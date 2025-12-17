# Migration Guide: v0.11.0

This guide covers all breaking changes in Rustica v0.11.0. For detailed migration steps, see the linked documents.

---

## Breaking Changes Overview

| Change | Impact | Details |
|--------|--------|---------|
| **Identity Trait Removed** | High | [identity-removal.md](docs/migration-v0.11.0/identity-removal.md) |
| **Choice API Cleanup** | Medium | [choice-changes.md](docs/migration-v0.11.0/choice-changes.md) |
| **Validated Typeclass Cleanup** | Medium | [validated-changes.md](docs/migration-v0.11.0/validated-changes.md) |
| **Either MonadPlus Removed** | Low | [either-changes.md](docs/migration-v0.11.0/either-changes.md) |
| **error_utils Module Moved** | Low | [error-utils-migration.md](docs/migration-v0.11.0/error-utils-migration.md) |
| **map_result Consolidated** | Low | [hkt-utils-changes.md](docs/migration-v0.11.0/hkt-utils-changes.md) |

---

## Quick Migration Summary

### Identity Trait Removal

```rust
// OLD
use rustica::traits::identity::Identity;
let value = option.value();

// NEW
let value = option.unwrap();
```

**Details**: [docs/migration-v0.11.0/identity-removal.md](docs/migration-v0.11.0/identity-removal.md)

---

### Choice API Changes

```rust
// OLD
use rustica::traits::monad_plus::MonadPlus;
let empty: Choice<i32> = <Choice<i32> as MonadPlus>::mzero();

// NEW
use rustica::traits::alternative::Alternative;
let empty: Choice<i32> = <Choice<i32> as Alternative>::empty_alt();
```

- MonadPlus removed (use Alternative)
- 17 utility methods deprecated
- Foldable no longer requires `T: Clone`

**Details**: [docs/migration-v0.11.0/choice-changes.md](docs/migration-v0.11.0/choice-changes.md)

---

### Validated Typeclass Cleanup

Removed implementations:

- `Monoid` - No lawful identity element
- `AsRef<A>` - Panicked on Invalid
- `MonadPlus`, `Alternative` - Conflicts with error accumulation

```rust
// OLD
let ref_val: &i32 = validated.as_ref(); // Could panic!

// NEW
if let Some(value) = validated.as_ref() { ... }
```

**Details**: [docs/migration-v0.11.0/validated-changes.md](docs/migration-v0.11.0/validated-changes.md)

---

### Either MonadPlus Removed

```rust
// OLD
let result = either1.mplus(&either2);

// NEW
use rustica::traits::alternative::Alternative;
let result = either1.alt(&either2);
```

**Details**: [docs/migration-v0.11.0/either-changes.md](docs/migration-v0.11.0/either-changes.md)

---

### error_utils Module Moved

```rust
// OLD
use rustica::utils::error_utils::{WithError, ResultExt};

// NEW
use rustica::error::{WithError, ResultExt};
```

Also removed: `AppError`, `error()`, `error_with_context()` → Use `ComposableError`

**Details**: [docs/migration-v0.11.0/error-utils-migration.md](docs/migration-v0.11.0/error-utils-migration.md)

---

### map_result Consolidated

```rust
// OLD (still works via re-export)
use rustica::utils::hkt_utils::map_result;

// NEW (preferred)
use rustica::utils::categorical_utils::map_result;
```

Signature changed from `Fn` to `FnOnce` (more flexible, backward compatible).

**Details**: [docs/migration-v0.11.0/hkt-utils-changes.md](docs/migration-v0.11.0/hkt-utils-changes.md)

---

## Timeline

- **v0.11.0**: Breaking changes applied, deprecations active
- **v0.12.0**: All deprecated items will be removed

---

## Working Examples

```bash
# Identity migration patterns
cargo run --example identity_migration_v0_11_0

# Choice migration patterns
cargo run --example choice_migration_v0_11_0
```

---

## Need Help?

1. Check the detailed migration guides linked above
2. Run the example code to see patterns in action
3. Open an issue if you have a use case that's not covered
