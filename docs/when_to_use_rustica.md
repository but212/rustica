# When to Use Rustica

Rustica is designed to bring expressive functional programming abstractions, compile-time impossible-state elimination, and composable error handling to Rust.

## When Rustica Shines

### 1. Complex Validation and Error Accumulation (`Validated`)

- **Use Case**: Form validation, configuration loading, API payload validation where you want to report **all** errors simultaneously rather than failing at the first error.
- **Why Rustica**: `Validated<E, T>` accumulates errors into `NonEmptyErrors<E>` via `Applicative::lift2`/`lift3` while guaranteeing that an invalid state always contains at least one error.

### 2. Guaranteed Non-Empty Alternative Selection (`Choice`)

- **Use Case**: Search fallbacks, routing fallbacks, multi-candidate resolution where a primary option is mandatory and alternatives are optional.
- **Why Rustica**: `Choice<T>` statically guarantees that empty choices cannot exist, avoiding runtime `unwrap()` panics.

### 3. Pure State Transitions & Context Passing (`State`, `Reader`, `StateT`, `ReaderT`)

- **Use Case**: Clean dependency injection, deterministic state machines, and pure functional pipelines.
- **Why Rustica**: Explicit encapsulation of environment and state transitions without mutable global state.

### 4. Immutable Persistent Collections (`PersistentVector`)

- **Use Case**: Undo/redo histories, branching tree calculations, functional data processing pipelines.
- **Why Rustica**: RRB-tree implementation with small-vector inline optimization and structural sharing.

---

## When to Prefer Standard Rust / Other Crates

| Requirement | Recommendation |
| --- | --- |
| Simple Optional Values | Use standard `Option<T>` (`Maybe<T>` was removed in 0.14.0) |
| Standard Success/Failure | Use standard `Result<T, E>` (`Either<L, R>` was removed in 0.14.0) |
| Production High-Throughput Caching | Use dedicated crates such as [`lru`](https://crates.io/crates/lru) or [`moka`](https://crates.io/crates/moka) |
| General Function Chaining | Use native Rust closures / method chaining directly |
