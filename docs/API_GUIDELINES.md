# Rustica API Guidelines: Naming and Receiver Conventions

Method naming conventions and receiver standards for Rustica, aligning the [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) with functional and persistent data structure semantics.

---

## 1. Core Ownership and Receiver Principles

| Receiver | Ownership Semantics | Primary Use Cases | Constraints and Anti-patterns |
| --- | --- | --- | --- |
| `&self` | Immutable Borrow | Inspection, queries, pure calculations, persistent structural sharing | No side effects; avoid forcing unnecessary `Clone` bounds |
| `&mut self` | Exclusive Borrow | In-place state mutation, buffer reuse | Cannot transfer ownership out of caller |
| `self` | Ownership Move | Type conversions, execution runners, termination, consuming builders | Do not use for read-only queries |

---

## 2. Conversion Methods (C-CONV)

Prefixes correspond strictly to receiver ownership and allocation cost:

| Prefix | Receiver | Cost | Return Type | Conventions |
| --- | --- | --- | --- | --- |
| `as_*` | `&self` / `&mut self` | Free | Borrowed reference (`&U`, `&mut U`) | Borrows internal view without allocation or copy (`as_slice`, `as_str`) |
| `to_*` | `&self` | Expensive | Owned value (`U`) | Clones or reallocates a new instance (`to_string`, `to_vec`, `to_pure`) |
| `into_*` | `self` | Move only | Owned value (`U`) | Consumes instance to unwrap or convert (`into_value`, `into_result`) |

### Rules and Examples

- **Never use `to_*` with a `self` receiver**: By-value methods must use `into_*`.
  - [BAD] `Validated::to_value(self)` -> [GOOD] `Validated::into_value(self)`
  - [BAD] `Free::into_pure(&self)` -> [GOOD] `Free::to_pure(&self)` (borrowing with clone requires `to_*`)
- **Never return an owned type from `as_*`**:
  - [BAD] `as_option(&self) -> Option<T>` (cloning `T`) -> [GOOD] `to_option(&self) -> Option<T>` or `as_option(&self) -> Option<&T>`

---

## 3. Getters and Accessors (C-GETTER)

Field getters omit the `get_` prefix.

### 3.1 Standard Rules

- **Bare identifiers**: `fn field(&self) -> &FieldType` ([BAD] `fn get_name(&self)` -> [GOOD] `fn name(&self)`)
- **Mutable getters**: `fn field_mut(&mut self) -> &mut FieldType`

### 3.2 Approved Exceptions for `get`

1. **Key/Index queries with failure**: `fn get(&self, index: usize) -> Option<&T>`
2. **Atomic/synchronization access**: `AtomicBool::get_mut(&mut self) -> &mut bool`
3. **Fallible lookups**: `fn try_get(&self, key: &K) -> Result<&V, Error>`

### 3.3 Execution Runners vs. Getters

Side-effect or computation triggers must never be named `get` or `try_get`:

- [BAD] `TryProgram::try_get(self, handler)` -> [GOOD] `TryProgram::try_run(self, handler)`
- `get` implies observation; `run` implies evaluation.

---

## 4. Builders and Setters (C-BUILDER)

### 4.1 Consuming Builders (Chaining)

- **Prefix**: `with_*` | **Receiver**: `mut self -> Self`
- Assembles immutable instances step-by-step by moving state:

```rust
impl ComposableError {
    pub fn with_error_code(mut self, code: u32) -> Self {
        self.error_code = Some(code);
        self
    }
}
```

### 4.2 In-Place Mutators (Setters)

- **Prefix**: `set_*` | **Receiver**: `&mut self -> ()`
- Mutates internal fields in-place on a bound instance (`Configuration::set_timeout(&mut self, timeout: Duration)`).

### 4.3 Borrowed Builders

- **Receiver**: `&mut self -> &mut Self` (reserved for large buffer or FFI assemblers).

---

## 5. Iterators (C-ITER)

Container types provide standard iterators where applicable:

| Method | Receiver | Item Type | Description |
| --- | --- | --- | --- |
| `iter(&self)` | `&self` | `&'a T` | Traverses by immutable reference |
| `iter_mut(&mut self)` | `&mut self` | `&'a mut T` | Traverses by mutable reference |
| `into_iter(self)` | `self` | `T` | Consumes container by value (`IntoIterator`) |

- **Domain Iterators**: `keys(&self) -> Keys<'_>`, `values(&self) -> Values<'_>`, `iter_errors(&self) -> std::slice::Iter<'_, E>`

---

## 6. Predicates and Boolean Queries (C-PREDICATE)

Boolean inspection methods always borrow via `&self`:

- `is_*`: State/variant query (`is_empty`, `is_valid`, `is_pure`)
- `has_*`: Component presence (`has_alternatives`)
- `can_*`: Capability check (`can_retry`)
- `contains`: Key or element containment (`contains(&self, item: &T)`)

---

## 7. Functional Programming and Domain Extensions

### 7.1 Structural Flattening and Filtering (`flatten`, `filter`)

- Structural transforms prefer **consuming `self`** to avoid forcing `T: Clone`:
  - Primary (consuming): `fn flatten<I>(self) -> Option<Self::Output<I>> where T: IntoIterator<Item = I>`
  - Borrowed companion: `fn flatten_cloned<I>(&self) -> ... where T: Clone`
  - Primary (consuming): `fn filter<F>(self, predicate: F) -> Option<Self>`
  - Borrowed companion: `fn filter_values<F>(&self, predicate: F) -> ... where T: Clone`

### 7.2 Monadic and Effect Computation Runners

- **Single-shot**: Consumes computation descriptor (`self`):
  - `Program::run(self, handler: &mut H) -> A`, `TryProgram::try_run(self, handler: &mut H) -> Result<A, E>`
- **Multi-shot (Documented Exception)**: Borrows `&self` when the pipeline is wrapped in `Arc<dyn Fn...>` and reusable across continuations:
  - `Free::run(&self, interp: Interp) -> A`, `Free::try_run(&self, interp: Interp) -> Result<A, FreeError<E>>`
  - Must document receiver rationale under **Receiver Semantics** in rustdoc.

### 7.3 Persistent Data Structures

Persistent collections return new roots with structural sharing (`Arc`) rather than mutating in place; mutation-like verbs use **`&self -> Self`**:

- `fn push_back(&self, value: T) -> Self`
- `fn update(&self, index: usize, value: T) -> Self`

### 7.4 Optics (Lens, Prism)

- Optics access and modification borrow `&self` (`Lens::get(&self, source: &S) -> A`, `Lens::set(&self, source: S, value: A) -> S`).
- Composition transfers unboxed closures, requiring `self` (`Lens::then(self, other: Lens<A, B>) -> Lens<S, B>`).

---

## 8. Naming and Receiver Checklist

| Pattern | Check | Correct Convention |
| --- | --- | --- |
| **Consuming Conversion** | Takes `self`, produces another type | `into_*` (`into_value`, `into_errors`, `into_result`) |
| **Cloned Conversion** | Takes `&self`, produces owned instance | `to_*` (`to_vec`, `to_string`, `to_option`, `to_pure`) |
| **Borrowed View** | Takes `&self`, borrows inner structure | `as_*` (`as_slice`, `as_str`, `as_bytes`) |
| **Field Getter** | Inspects field value | `field(&self)`, `field_mut(&mut self)` (no `get_`) |
| **Key/Index Lookup** | Fallible query by key or position | `get(&self, key)` |
| **Consuming Builder** | `mut self`, updates field, returns `Self` | `with_*` (`with_error_code`, `with_context`) |
| **In-place Setter** | `&mut self`, updates field in-place | `set_*` (`set_timeout`, `set_code`) |
| **Predicate** | Boolean state query | `is_*`, `has_*`, `can_*`, `contains` (always `&self`) |
| **Computation Runner** | Evaluates effect or state computation | `run(self)`, `try_run(self)` (distinct from `get`) |
| **Collection Flatten/Filter** | Structural consumption without `Clone` | Primary `flatten(self)`, `filter(self)` |
