# Rustica Design Philosophy and Architectural Principles

This document defines the architectural trade-offs and boundary principles governing Rustica, detailing how the library reconciles pure functional abstractions with idiomatic, zero-cost Rust.

---

## 1. Core Philosophy: Functional Tools for Idiomatic Rust

Rustica provides functional programming abstractions designed to work with, rather than against, the Rust language model.

Directly porting Haskell-style category-theoretic and monadic patterns into Rust introduces severe structural friction: monomorphized combinator chains inflate compile times, `dyn Fn` traits force heap allocations, and closure environments leak lifetime parameters into public signatures. Rustica rejects dogmatic category theory in favor of zero-cost performance and standard idiom alignment (see §2.6).

### Guiding Principles

1. **Native Rust Primitives First:** State management, execution, and control flow belong to Rust primitives (`&mut`, `&`, `?`, `async`/`await`, pattern matching). Rustica avoids monadic wrappers where native constructs are already zero-cost and expressive.
2. **Solve Unaddressed Domain Gaps:** Rustica targets capabilities absent from the standard library: multi-error accumulation (`Validated`), ordered fallback execution (`Choice`), composable optics (`Lens`, `Prism`), and interpreter ASTs (`Free`, `Program`).

---

## 2. Structural Friction Points: Functional Patterns in Rust

Pure functional programming assumes a garbage-collected runtime, pervasive laziness, and first-class type constructors. Mapping these assumptions to Rust reveals five structural friction points. Sections 2.1–2.5 define these constraints; §2.6 details the resulting architectural trade-offs.

| Dimension | Conflict Summary | Native Rust Resolution |
| --- | --- | --- |
| **1. Ownership & Lifetimes** | Affine moves vs. persistent garbage-collected values | Explicit borrowing (`&Context`), exclusive mutation (`&mut S`), amortized buffers |
| **2. Type System** | GAT simulation vs. native Higher-Kinded Types & currying | Inherent methods, standard closures, concrete generic types |
| **3. Compilation & Runtime** | Monomorphization explosion vs. `dyn Fn` / No TCO | Zero-cost inline closures, iterative traversal loops |
| **4. Syntactic Ergonomics** | Nested closure callbacks vs. native operators | Native `?` error propagation, `async`/`await`, pattern matching |
| **5. Ecosystem Cohesion** | Bespoke functional wrappers vs. standard vocabulary | Direct interoperability with `Option`, `Result`, `Iterator`, and `Future` |

### 2.1 Ownership and Lifetimes

- **State Threading:** Simulating immutable state threading (`State s a`) requires continuous snapshot cloning or awkward ownership handoffs. Exclusive borrowing (`&mut S`) delivers statically verified in-place mutation at zero runtime cost.
- **Environment Injection:** Functional environment passing (`Reader e a`) forces lifetime parameters into closure types, pushing implementations toward redundant cloning. Native immutable borrowing (`&Context`) shares read-only state without allocation.
- **Accumulation and Allocation:** Monadic logging (`Writer<W, A>`) produces new values via associative combination, inducing quadratic reallocations on contiguous collections. Rust expresses logging via mutable buffers (`&mut Buffer`) or structured diagnostic events. Consuming workflows minimize clones by moving owned values directly and unwrapping unique references (`Arc::try_unwrap`).

### 2.2 Type System Limitations

- **Absence of Higher-Kinded Types (HKT):** Rust lacks first-class type constructors (`F<_>`). While Generic Associated Types (GATs) simulate unary type constructors, multi-parameter transformer stacks break down under verbose turbofish annotations and brittle type inference.
- **Absence of Currying:** Rust functions have fixed arity. Emulating partial application via manual closure wrapping or combinatorial macros (`lift2`, `lift3`) introduces syntactic clutter without architectural benefit.

### 2.3 Compilation and Runtime Constraints

- **Monomorphization vs. Dynamic Dispatch:** Deep functional combinator chains force a compromise between compile-time bloat (unique closure monomorphization risking recursive type limits) and runtime penalty (heap-allocated `dyn Fn` vtables).
- **Absence of Tail Call Optimization (TCO):** Rust does not guarantee TCO. Unbounded monadic recursion (`bind` chains in `IO`, `Free`, or `Cont`) causes runtime stack exhaustion, requiring explicit trampolines or iterative evaluation loops.

### 2.4 Syntactic Ergonomics and Control Flow

Without language-level `do`-notation or comprehensions, monadic composition degrades into deeply nested closure pyramids. Native Rust operators (`?`, `async`/`await`, pattern matching) achieve linear, idiomatic control flow with direct compiler error diagnostics and zero abstraction overhead.

### 2.5 Ecosystem Cohesion

Replacing standard library primitives with bespoke functional counterparts (`Maybe` for `Option`, `Either` for `Result`, `Id` for plain values) isolates code from standard ecosystem tooling, serialization frameworks, and async runtimes, creating pervasive conversion overhead at API boundaries.

### 2.6 What Is Given Up

Replacing `Reader`, `State`, and `Writer` with `&Context`, `&mut S`, and `&mut Buffer` sacrifices specific compositional properties:

- **`Reader`:** Type-level, ambient dependency injection across arbitrary call stacks without parameter threading.
- **`State`:** Reified, inspectable state transitions that can be paused, reordered, or replayed.
- **`Writer`:** Decoupled log generation where callers dictate consumption strategy without branching at production sites.

In idiomatic Rust, these compositional guarantees rarely justify their runtime and ergonomics penalties (§2.1–§2.3). Rustica deliberately accepts this trade-off, restricting monadic composition to explicit domain models such as DSL interpretation (`Free`) and operational handler pipelines (`Program`).

---

## 3. Core Library Identity

Rustica maintains functional abstractions strictly where they solve concrete engineering problems that the standard library leaves unaddressed:

| Component | Target Problem | Standard Library Contrast |
| --- | --- | --- |
| **`Validated<T, E>`** | Multi-error domain validation | Unlike `Result` (which short-circuits on first failure), accumulates all constraint violations. |
| **`Choice<T>`** | Priority & fallback execution | Statically non-empty target sequences with integrated multi-target error diagnostics (`try_each`, `try_each_validated`). |
| **`Free<F, A>`** | DSL AST construction & multi-pass analysis | Reusable, inspectable computation tree for multi-pass interpretation and AST analysis with explicit `Then` sequencing and encapsulated type-erasure. |
| **`Program<H, A>`** | Direct operational monad execution | Statically checked handler pipelines with compile-time command-to-output enforcement and trampoline evaluation. |
| **Optics (`Lens`, `Prism`)** | Composable access into nested data | Pure, reusable paths for querying and immutably updating deeply nested structs and enum variants. |
| **Algebraic Traits (`Semigroup`, `Monoid`)** | Generic combination and identity interfaces | Associative combination across concrete types, powering error accumulation in `Validated` and fallback chains in `Choice`. *(Categorical simulation traits removed in 0.19.0 in favor of native Rust idioms).* |

---

## 4. Architectural Boundary Matrix

This matrix guides component selection between standard Rust idioms and Rustica domain types:

| Problem | Anti-Pattern (Deprecated) | Idiomatic Rust Standard | Rustica Domain Solution |
| --- | --- | --- | --- |
| State threading (§2.1) | `State<S, A>`, `StateT` | `&mut S` or `Fn(S) -> (A, S)` | *— not provided; use standard idiom* |
| Environment sharing (§2.1) | `Reader<E, A>`, `ReaderT` | `&Context` / lexical closures | *— not provided; use standard idiom* |
| Execution logging (§2.1) | `Writer<W, A>` | `&mut Buffer` / structured logging | *— not provided; use standard idiom* |
| Deferred execution (§2.3) | `IO<A>` | Plain closures `\|\| ...` / `async` | *— not provided; use standard idiom* |
| Boolean evaluation | `Predicate<A>` | Closures `\|x\| ...` / `&&`, `\|\|`, `!` | *— not provided; use standard idiom* |
| Monoidal reduction | `Sum`, `Product`, `Min`, `Max` | `Iterator::sum`, `product`, `min`, `max` | *— not provided; use standard idiom* |
| Primary / fallback tasks | Nested loops / `Choice::bind` | `Iterator::find_map` | `Choice::try_each` |
| Fallback with full audit | Manual error accumulation loops | Explicit error vectors | `Choice::try_each_validated` |
| Multi-field validation | `Result<T, Vec<E>>` (early bail) | `Result<T, E>` with `?` | `Validated<T, E>` |
| Reusable DSL AST / Multi-run tree | Complex macro ASTs | Ad-hoc enum AST parser | `Free<F, A>` |
| Static operational execution | Dynamic downcasting dispatch | Match loops over enums | `Program<H, A>` / `TryProgram<H, A, E>` |
| Nested struct updates | Manual clone-and-assign | In-place mutable setters | `Lens::set`, `Lens::then` |
| Deep enum branching | Nested `match` blocks | `if let` matching | `Prism::preview`, `Prism::then` |

---

## 5. Summary

Rustica embraces Rust's native ownership, affine types, and native operators over emulating foreign paradigms. Delegating state, side effects, and control flow to the borrow checker removes layer upon layer of indirection, trading off monadic abstraction flexibility where standard idioms excel (§2.6).

The result is a zero-cost, idiom-aligned library focused solely on functional domains the standard library leaves unsolved.
