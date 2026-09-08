# Rustica API Guidelines: Naming and Receiver Conventions

This document establishes method naming conventions and self receiver design standards for the Rustica project, combining the official Rust API Guidelines (<https://rust-lang.github.io/api-guidelines/>) with functional programming and persistent data structure domain rules.

---

## 1. Core Ownership and Receiver Principles

| Receiver | Ownership Semantics | Primary Use Cases | Constraints and Anti-patterns |
| --- | --- | --- | --- |
| `&self` | Immutable Borrow | Inspection, queries, pure calculations, structural sharing in persistent collections | No side effects; avoid forcing unnecessary Clone bounds |
| `&mut self` | Exclusive Borrow | In-place internal state mutation, buffer reuse | Cannot transfer ownership out of the caller |
| `self` | Ownership Move (Consume) | Type conversions, execution runners, termination, consuming builder chaining | Do not use for read-only queries (prevents instance dropping) |

---

## 2. Conversion Methods (C-CONV)

Conversion method prefixes strictly correspond to the cost and ownership semantics of the receiver.

| Prefix | Receiver | Cost | Return Type | Description and Conventions |
| --- | --- | --- | --- | --- |
| `as_*` | `&self` / `&mut self` | Free | Borrowed reference (`&U`, `&mut U`) | Borrows a view into internal data without allocation or copying (e.g., `as_slice(&self) -> &[T]`, `as_str(&self) -> &str`) |
| `to_*` | `&self` | Expensive | Owned value (`U`) | Retains the original instance and produces a new value via cloning or heap reallocation (e.g., `to_string(&self) -> String`, `to_vec(&self) -> Vec<T>`) |
| `into_*` | `self` | Variable (typically move only) | Owned value (`U`) | Consumes the original instance by value to unwrap or convert into another type (e.g., `into_inner(self) -> T`, `into_state(self) -> State<S, A>`) |

### Rules and Examples

- **Never use `to_*` with a `self` receiver**: Methods taking `self` by value must be named `into_*`.
  - [BAD] `StateT::to_state(self)` -> [GOOD] `StateT::into_state(self)`
  - [BAD] `WithError::to_result(self)` -> [GOOD] `WithError::into_result(self)`
- **Never return an owned type from `as_*`**:
  - [BAD] `as_option(&self) -> Option<T>` (when cloning `T`) -> [GOOD] `to_option(&self) -> Option<T>` or `as_option(&self) -> Option<&T>`

---

## 3. Getters and Accessors (C-GETTER)

Following Rust conventions, field getters omit the `get_` prefix.

### 3.1 Standard Rules

- **Bare identifier for getters**:
  - `fn field(&self) -> &FieldType`
  - [BAD] `fn get_name(&self) -> &str` -> [GOOD] `fn name(&self) -> &str`
- **Mutable getters**:
  - `fn field_mut(&mut self) -> &mut FieldType`
  - E.g., `fn value_mut(&mut self) -> &mut T`

### 3.2 Approved Exceptions for `get`

The `get` prefix is reserved for operations that:

1. **Query by index or key with potential failure**:
   - `fn get(&self, index: usize) -> Option<&T>`
   - `fn get_mut(&mut self, index: usize) -> Option<&mut T>`
2. **Perform atomic/synchronization access**:
   - `AtomicBool::get_mut(&mut self) -> &mut bool`
3. **Perform fallible lookups**:
   - `fn try_get(&self, key: &K) -> Result<&V, Error>`

### 3.3 Execution Runners vs. Getters

Methods that trigger side effects or evaluate computations must never be named `get` or `try_get`.

- [BAD] `IO::try_get(self)` -> [GOOD] `IO::try_run(self)`
- `get` implies read-only observation; `run` implies evaluation and execution.

---

## 4. Builders and Setters (C-BUILDER)

Builder and mutator patterns are separated by receiver type:

### 4.1 Consuming Builders (Chaining)

- **Prefix**: `with_*` (or domain-specific action)
- **Receiver**: `mut self -> Self`
- **Purpose**: Assembles immutable instances step-by-step, moving the previous state.
- Example:

  ```rust
  impl ComposableError {
      pub fn with_error_code(mut self, code: u32) -> Self {
          self.error_code = Some(code);
          self
      }
  }
  ```

### 4.2 In-Place Mutators (Setters)

- **Prefix**: `set_*`
- **Receiver**: `&mut self -> ()`
- **Purpose**: Modifies internal fields in-place on an already-bound mutable instance.
- Example:

  ```rust
  impl Configuration {
      pub fn set_timeout(&mut self, timeout: Duration) {
          self.timeout = timeout;
      }
  }
  ```

### 4.3 Non-Consuming Borrowed Builders

- **Receiver**: `&mut self -> &mut Self`
- Used primarily for large buffer assemblers or FFI struct builders.

---

## 5. Iterators (C-ITER)

Container types should provide the standard iterator triplet where applicable:

| Method | Receiver | Item Type | Description |
| --- | --- | --- | --- |
| `iter(&self)` | `&self` | `&'a T` | Traverses by immutable reference |
| `iter_mut(&mut self)` | `&mut self` | `&'a mut T` | Traverses by mutable reference |
| `into_iter(self)` | `self` | `T` | Consumes container by value (`IntoIterator` implementation) |

- **Domain-Specific Iterators**:
  - `keys(&self) -> Keys<'_>`, `values(&self) -> Values<'_>`
  - `iter_errors(&self) -> IterErrors<'_>` (traverses dedicated components)

---

## 6. Predicates and Boolean Queries (C-PREDICATE)

Methods returning `bool` inspect state and must always borrow via `&self`:

- `is_*`: State or variant queries (`is_empty(&self)`, `is_valid(&self)`, `is_pure(&self)`)
- `has_*`: Component presence queries (`has_alternatives(&self)`)
- `can_*`: Capability/feasibility checks (`can_retry(&self)`)
- `contains`: Element or key containment checks (`contains(&self, item: &T)`)

---

## 7. Functional Programming and Domain Extensions

Specialized guidelines for Rustica's categorical and persistent abstractions:

### 7.1 Structural Flattening and Filtering (`flatten`, `filter`)

- Operations that transform collections by structure should prefer **consuming `self` receivers** as the primary API.
- Using `&self` as the default forces a `T: Clone` bound, preventing use with move-only types.
  - Primary (consuming): `fn flatten<I>(self) -> Option<Self::Output<I>> where T: IntoIterator<Item = I>`
  - Borrowed companion: `fn flatten_cloned<I>(&self) -> ... where T: Clone`
  - Primary (consuming): `fn filter<F>(self, predicate: F) -> Option<Self>`
  - Borrowed companion: `fn filter_values<F>(&self, predicate: F) -> ... where T: Clone`

### 7.2 Monadic and Effect Computation Runners

- **Single-shot Computations**:
  - Evaluates side effects or state transitions by consuming the computation descriptor: `self` receiver.
  - `IO::run(self) -> O`, `State::run_state(self, s: S) -> (A, S)`, `Program::run(self, handler: &mut H) -> A`, `TryProgram::try_run(self, handler: &mut H) -> Result<A, E>`
- **Multi-shot Computations (Documented Exception)**:
  - When the execution pipeline is wrapped in an `Arc<dyn Fn...>`, allowing the same computation to be executed multiple times with different continuations, `&self` is permitted.
  - Must document receiver rationale under a dedicated **Receiver Semantics** section in rustdoc.
  - `Cont::run(&self, k: FN) -> R`, `Free::run(&self, interp: Interp) -> A`, `Free::try_run(&self, interp: Interp) -> Result<A, FreeError<E>>`

### 7.3 Persistent Data Structures

- Persistent collections (`PersistentVector`, `RRBTree`) return newly allocated roots with structural sharing (via `Arc`) rather than mutating in place.
- Therefore, mutation-like verbs use **`&self -> Self`** instead of `&mut self`.
  - `fn push_back(&self, value: T) -> Self`
  - `fn update(&self, index: usize, value: T) -> Self`

### 7.4 Optics (Lens, Prism)

- Optics are reusable first-class functional references; access and modification operations borrow `&self`:
  - `Lens::get(&self, source: &S) -> A`
  - `Lens::set(&self, source: S, value: A) -> S`
- Composition of optics transfers unboxed closures into the combined optic, requiring `self`:
  - `Lens::then(self, other: Lens<A, B>) -> Lens<S, B>`

---

## 8. Naming and Receiver Checklist

| Pattern | Check | Correct Convention |
| --- | --- | --- |
| **Consuming Conversion** | Takes `self`, produces another type | `into_*` (`into_state`, `into_log`, `into_result`) |
| **Cloned Conversion** | Takes `&self`, produces owned instance | `to_*` (`to_vec`, `to_string`, `to_option`) |
| **Borrowed View** | Takes `&self`, borrows inner structure | `as_*` (`as_slice`, `as_str`, `as_bytes`) |
| **Field Getter** | Inspects field value | `field(&self)`, `field_mut(&mut self)` (no `get_`) |
| **Key/Index Lookup** | Fallible query by key or position | `get(&self, key)` |
| **Consuming Builder** | `mut self`, updates field, returns `Self` | `with_*` (`with_error_code`, `with_context`) |
| **In-place Setter** | `&mut self`, updates field in-place | `set_*` (`set_timeout`, `set_code`) |
| **Predicate** | Boolean state query | `is_*`, `has_*`, `can_*`, `contains` (always `&self`) |
| **Computation Runner** | Evaluates effect or state computation | `run(self)`, `try_run(self)` (distinct from `get`) |
| **Collection Flatten/Filter** | Structural consumption without `Clone` | Primary `flatten(self)`, `filter(self)` |
