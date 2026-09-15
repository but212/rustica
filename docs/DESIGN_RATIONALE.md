# Rustica Design Philosophy and Architectural Principles

This document outlines the design philosophy, architectural trade-offs, and boundary principles governing Rustica's functional abstractions, explaining how the library reconciles pure functional patterns with idiomatic Rust.

---

## 1. Core Philosophy: Functional Tools for Idiomatic Rust

Rustica provides functional programming abstractions designed to work with, rather than against, the Rust language.

Many functional libraries attempt to port Haskell-style category-theoretic and monadic patterns directly into Rust. Experience across releases v0.13.0 through v0.17.0 demonstrated that pure functional abstractions often conflict with Rust's ownership model, type system, compilation strategy, and language-level control flow. Direct ports tend to produce compromises: they lack the syntactic conciseness of pure languages while introducing unnecessary allocations, indirection, and compiler friction in Rust.

### Guiding Principles

1. **Native Rust Primitives First:** Execution, state management, and control flow belong to Rust's native language features (`&mut`, `&`, `?`, `async`/`await`, and monomorphized closures). Rustica does not provide monadic wrappers where standard language constructs are already zero-cost and expressive.
2. **Solve Unaddressed Domain Gaps:** Rustica focuses on capabilities absent from the standard library: multi-error accumulation (`Validated`), ordered fallback execution (`Choice`), persistent structural sharing (`PersistentVector`), and compositional optics (`Lens`, `Prism`).
3. **Mechanical Sympathy:** All abstractions must respect Rust's affine types, borrow checker, and memory layouts without requiring hidden allocations or artificial `Clone` constraints.

---

## 2. Structural Friction Points: Functional Patterns in Rust

Pure functional programming assumes a garbage-collected runtime with uniform boxed values, pervasive laziness, and first-class type constructors. Mapping these patterns to Rust exposes five structural friction points:

| Dimension | Conflict Summary | Native Rust Resolution |
| --- | --- | --- |
| **1. Ownership & Lifetimes** | Affine moves vs. persistent garbage-collected values | Explicit borrowing (`&Context`), exclusive mutation (`&mut S`), amortized buffers |
| **2. Type System** | GAT simulation vs. native Higher-Kinded Types & currying | Inherent methods, standard closures, concrete generic types |
| **3. Compilation & Runtime** | Monomorphization explosion vs. `dyn Fn` / No TCO | Zero-cost inline closures, iterative traversal loops |
| **4. Syntactic Ergonomics** | Nested closure callbacks vs. native operators | Native `?` error propagation, `async`/`await`, pattern matching |
| **5. Ecosystem Cohesion** | Bespoke functional wrappers vs. standard vocabulary | Direct interoperability with `Option`, `Result`, `Iterator`, and `Future` |

### 2.1 Ownership and Lifetimes

- **State threading:** Haskell's `State s a` threads state immutably as `s -> (a, s)`. In Rust, exclusive borrowing (`&mut S`) provides statically verified in-place mutation at zero cost. Simulating `State` forces snapshot cloning or complicated ownership transfers across function boundaries.
- **Environment injection:** Haskell's `Reader e a` implicitly passes shared configuration. In Rust, immutable borrows (`&Context`) achieve this without allocation. Storing references inside monadic closures introduces complex lifetime parameters (`'a`), pushing implementations toward cloning owned environments.
- **Log accumulation:** Monadic `Writer<W, A>` combines logs through `W::combine`. For contiguous buffers (`String`, `Vec`), this produces quadratic reallocation cascades ($O(N^2)$). Idiomatic Rust relies on amortized $O(1)$ in-place mutation (`&mut Buffer`) or dedicated logging facades (`tracing`).

### 2.2 Type System Limitations

- **Absence of Higher-Kinded Types (HKT):** Rust lacks first-class type constructors (`F<_>`). Simulating HKT via Generic Associated Types (`trait HKT { type Output<B>; }`) works for single-parameter types, but breaks down under multi-parameter transformer stacks (`StateT`, `ReaderT`, `BinaryHKT`), requiring verbose turbofish annotations.
- **Absence of Currying:** Rust functions have fixed arity `fn(A, B) -> C`. Partial application requires explicit closure construction (`|b| f(a, b)`) or combinatorial macros (`lift2`, `lift3`), adding visual clutter and API bloat.

### 2.3 Compilation and Runtime Constraints

- **Monomorphization vs. Dynamic Dispatch:** Deep functional pipelines face a trade-off:
  - *Monomorphization:* Every combinator generates a distinct closure type, compounding compilation times and risking infinite-size recursion errors in recursive ASTs.
  - *Dynamic Dispatch (`Arc<dyn Fn>`):* Eliminates type growth, but introduces heap allocations, atomic reference counting, and indirect vtable calls at every step.
- **Absence of Tail Call Optimization (TCO):** Rust does not guarantee TCO. Recursive monadic chaining (`bind(f).bind(g)...` in `IO`, `Free`, or `Cont`) risks runtime stack overflow in release builds, requiring manual trampoline loops or iterative interpretation.

### 2.4 Ergonomics and Control Flow

Without `do`-notation or comprehensions, monadic composition in Rust degrades into nested closure pyramids:

```rust
// Monadic closure nesting
get_a().bind(|a| get_b(a).bind(|b| Pure::pure(compute(a, b))))
```

Rust's native operators achieve linear execution with clearer error reporting and zero abstraction overhead:

```rust
// Idiomatic Rust
let a = get_a()?;
let b = get_b(a)?;
compute(a, b)
```

### 2.5 Ecosystem Cohesion

Replacing standard types with custom functional equivalents (`Maybe` for `Option`, `Either` for `Result`, `Id` for plain values) isolates code from the wider ecosystem (`serde`, `tokio`, standard traits), requiring conversion shims at every boundary.

---

## 3. Library Evolution (v0.13.0 to v0.17.0)

Rustica's release history reflects a consistent transition from broad functional emulation to targeted domain utility:

| Release | Focus | Key Actions | Architectural Rationale |
| --- | --- | --- | --- |
| **v0.13.0** | Pruning dead utilities & bounds | Removed point-free utilities (`compose`, `pipe`, `flip`); relaxed `Clone` bounds on moves; aliased `id` to `std::convert::identity`. | Point-free combinators added noise; artificial `Clone` bounds hindered moves. |
| **v0.14.0** | Retiring duplicate sum types | Replaced `Maybe<T>` with `Option<T>` and `Either<L, R>` with `Result<R, L>`; removed `Comonad`, `Category`, `Arrow`. | Standard types already implement functional traits without ecosystem friction. |
| **v0.15.0** | Mathematical invariants & fluent APIs | Removed `Monad` from `Validated` (enforcing lawful `Applicative` error accumulation); adopted left-to-right chaining (`then`); deprecated separate `*_owned` variants. | `Validated` cannot lawfully implement `Monad` without discarding errors; fluent chaining improves readability. |
| **v0.16.0** | API conventions & semantic refocusing | Aligned with Rust API Guidelines (`C-CONV`, `C-BUILDER`, `C-GETTER`); redefined `Choice` from Cartesian monad to fallback execution (`try_each`); feature-gated `pvec`. | Cartesian `Choice::bind` caused exponential branching; persistent vector overhead should be opt-in. |
| **v0.17.0** | Retiring simulated effect monads | Deprecated `State`, `Reader`, `Writer`, `IO`, `Cont`, `transformers`, `FunctionCategory`, `Predicate`, and monoidal newtypes (`Sum`, `Product`, etc.). | Native language primitives (`&mut`, `&`, `?`, closures) strictly supersede simulated effect monads. |
| **v0.18.0** *(Target)* | Consolidated core | Complete removal of all APIs deprecated in v0.16.0 and v0.17.0. | Finalizes lean, zero-cost core. |

---

## 4. Core Library Identity

Rustica retains functional abstractions where they solve concrete engineering problems that the Rust standard library does not address:

| Component | Target Problem | Standard Library Contrast |
| --- | --- | --- |
| **`Validated<E, A>`** | Multi-error domain validation | Unlike `Result` (which short-circuits on the first failure), accumulates all constraint violations. |
| **`Choice<T>`** | Priority & fallback execution | Statically non-empty target sequences with integrated multi-target error diagnostics (`try_each`, `try_each_validated`). |
| **`PersistentVector<T>`** (`pvec`) | Structural sharing for immutable collections | 32-way RRB-Tree enabling $O(\log n)$ updates and branch sharing without copying full buffers. |
| **Optics (`Lens`, `Prism`)** | Composable access into nested data | Pure, reusable paths for querying and immutably updating deeply nested structs and enum variants. |
| **Algebraic Traits** | Generic abstractions | `Semigroup`, `Monoid`, `Functor`, `Applicative`, `Monad`, `Foldable` implemented strictly where ownership rules are respected. |

---

## 5. Architectural Boundary Matrix

This matrix provides a guide for choosing between standard Rust idioms and Rustica's domain types:

| Problem | Anti-Pattern (Deprecated) | Idiomatic Rust Standard | Rustica Domain Solution |
| --- | --- | --- | --- |
| State threading | `State<S, A>`, `StateT` | `&mut S` or `Fn(S) -> (A, S)` | — |
| Environment sharing | `Reader<E, A>`, `ReaderT` | `&Context` / lexical closures | — |
| Execution logging | `Writer<W, A>` | `&mut Buffer` / `tracing` facade | — |
| Deferred execution | `IO<A>` | Plain closures `\|\| ...` / `async` | — |
| Boolean evaluation | `Predicate<A>` | Closures `\|x\| ...` / `&&`, `\|\|`, `!` | — |
| Monoidal reduction | `Sum`, `Product`, `Min`, `Max` | `Iterator::sum`, `product`, `min`, `max` | — |
| Primary / fallback tasks | Nested loops / `Choice::bind` | `Iterator::find_map` | `Choice::try_each` |
| Fallback with full audit | Manual error accumulation loops | Explicit error vectors | `Choice::try_each_validated` |
| Multi-field validation | `Result<T, Vec<E>>` (early bail) | `Result<T, E>` with `?` | `Validated<E, A>` |
| Structural sharing | Full clone (`Vec::clone`) | `Arc<Vec<T>>` | `PersistentVector<T>` |
| Nested struct updates | Manual clone-and-assign | In-place mutable setters | `Lens::set`, `Lens::then` |
| Deep enum branching | Nested `match` blocks | `if let` matching | `Prism::preview`, `Prism::then` |

---

## 6. Summary

Rustica's design evolution reflects a deliberate transition from emulating a foreign paradigm to embracing Rust's native model. Delegating state, side-effects, and control flow to the borrow checker, affine types, and native operators eliminates unnecessary indirection.

The result is a focused library that provides functional capabilities where Rust developers need them most, without compromising zero-cost performance or language conventions.
