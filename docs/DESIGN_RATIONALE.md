# Rustica Design Philosophy and Architectural Principles

This document outlines the design philosophy, architectural trade-offs, and boundary principles governing Rustica's functional abstractions, explaining how the library reconciles pure functional patterns with idiomatic Rust.

---

## 1. Core Philosophy: Functional Tools for Idiomatic Rust

Rustica provides functional programming abstractions designed to work with, rather than against, the Rust language.

Porting Haskell-style category-theoretic and monadic patterns directly into Rust incurs measurable engineering costs across ownership, typing, and compilation: monomorphized combinator chains lengthen build times, `Arc<dyn Fn>` bounds introduce heap allocations, and closure captures leak lifetime parameters into public APIs.

This is an intentional design trade-off rather than an impossibility: prioritizing zero-cost performance and idiom alignment means trading off certain compositional guarantees (see §2.6).

### Guiding Principles

1. **Native Rust Primitives First:** Execution, state management, and control flow belong to Rust's native language features (`&mut`, `&`, `?`, `async`/`await`, and monomorphized closures). Rustica does not provide monadic wrappers where standard language constructs are already zero-cost and expressive.
2. **Solve Unaddressed Domain Gaps:** Rustica focuses on capabilities absent from the standard library: multi-error accumulation (`Validated`), ordered fallback execution (`Choice`), persistent structural sharing (`PersistentVector`, deprecated in 0.18.0 for 0.19.0 removal), and compositional optics (`Lens`, `Prism`).

---

## 2. Structural Friction Points: Functional Patterns in Rust

Pure functional programming assumes a garbage-collected runtime, pervasive laziness, and first-class type constructors. Mapping these patterns to Rust reveals five structural friction points. Sections 2.1–2.4 cover language-level constraints; §2.6 discusses the trade-offs of Rustica's resolutions.

| Dimension | Conflict Summary | Native Rust Resolution |
| --- | --- | --- |
| **1. Ownership & Lifetimes** | Affine moves vs. persistent garbage-collected values | Explicit borrowing (`&Context`), exclusive mutation (`&mut S`), amortized buffers |
| **2. Type System** | GAT simulation vs. native Higher-Kinded Types & currying | Inherent methods, standard closures, concrete generic types |
| **3. Compilation & Runtime** | Monomorphization explosion vs. `dyn Fn` / No TCO | Zero-cost inline closures, iterative traversal loops |
| **4. Syntactic Ergonomics** | Nested closure callbacks vs. native operators | Native `?` error propagation, `async`/`await`, pattern matching |
| **5. Ecosystem Cohesion** | Bespoke functional wrappers vs. standard vocabulary | Direct interoperability with `Option`, `Result`, `Iterator`, and `Future` |

### 2.1 Ownership and Lifetimes

- **State threading:** Haskell's `State s a` threads state immutably as `s -> (a, s)`. In Rust, exclusive borrowing (`&mut S`) provides statically checked in-place mutation at zero cost. Simulating `State` forces snapshot cloning or awkward ownership transfers.
- **Environment injection:** Haskell's `Reader e a` implicitly passes shared configuration. In Rust, immutable borrows (`&Context`) share context without allocation. Embedding references in monadic closures introduces lifetime parameters (`'a`), pushing implementations toward cloning owned environments.
- **Log accumulation:** In Haskell, pure functions require a monadic wrapper (`Writer<W, A>`) to return a side-channel log alongside a value. Rust expresses this directly with a plain tuple `(A, W)`, a mutable reference (`&mut Buffer`), or structured logging without `bind` chains. Because `W::combine` returns a new value rather than mutating in place, monadic chaining also causes quadratic reallocations ($O(N^2)$) on contiguous buffers (`String`, `Vec`) that in-place mutation avoids.
- **Minimizing redundant clones in consuming workflows:** When an API operates by ownership (such as `monoid::repeat(value, n)`, `PersistentVectorIntoIter`, or recursive trampolines in `Free`), operations consume owned values directly on the final combination step and unwrap uniquely owned pointers (`Arc::try_unwrap`) to eliminate redundant clones.

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

Replacing standard types with custom functional equivalents (`Maybe` for `Option`, `Either` for `Result`, `Id` for plain values) isolates code from the wider ecosystem (serialization frameworks, asynchronous runtimes, standard traits), requiring conversion shims at every boundary.

### 2.6 What Is Given Up

Replacing `Reader`, `State`, and `Writer` with `&Context`, `&mut S`, and `&mut Buffer` trades off specific compositional guarantees:

- **`Reader`** provided type-level, scope-independent dependency injection for swapping execution environments (e.g., test doubles) without manual parameter threading.
- **`State`** reified state transitions as composable, reorderable values, useful for interpreters and transition replay.
- **`Writer`** decoupled log production from consumption, allowing one computation to be interpreted multiple ways (e.g., discard or reroute logs) without call-site branches.

These guarantees rarely justify their runtime and ergonomics costs in typical Rust systems (§2.1–§2.3), where native constructs suffice. However, codebases structured around interpreters or effect pipelines may find native replacements less composable.

---

## 3. Core Library Identity

Rustica retains functional abstractions where they solve concrete engineering problems that the Rust standard library does not address:

| Component | Target Problem | Standard Library Contrast |
| --- | --- | --- |
| **`Validated<T, E>`** | Multi-error domain validation | Unlike `Result` (which short-circuits on the first failure), accumulates all constraint violations. |
| **`Choice<T>`** | Priority & fallback execution | Statically non-empty target sequences with integrated multi-target error diagnostics (`try_each`, `try_each_validated`). |
| **`PersistentVector<T>`** (`pvec`) | Structural sharing for immutable collections | 32-way RRB-Tree enabling $O(\log n)$ updates and branch sharing without copying full buffers. *(Deprecated in 0.18.0, removal in 0.19.0; migrate to `imbl`)* |
| **`Free<F, A>`** | DSL AST construction & multi-pass analysis | Reusable, cloneable computation tree for inspectable and re-interpretable DSL ASTs. Fully supported alongside operational pipelines. |
| **`Program<H, A>`** | Direct operational monad execution | Statically checked handler pipelines with compile-time command-to-output enforcement and trampoline evaluation. |
| **Optics (`Lens`, `Prism`)** | Composable access into nested data | Pure, reusable paths for querying and immutably updating deeply nested structs and enum variants. |
| **Algebraic Traits (`Semigroup`, `Monoid`)** | Generic combination and identity interfaces | Associative combination across concrete types (`*`), powering error accumulation in `Validated` and fallback chains in `Choice` without GAT or HKT complexity. *(Functor, Applicative, Monad, Foldable, Pure, HKT deprecated in 0.18.0 for 0.19.0 removal).* |

---

## 4. Architectural Boundary Matrix

This matrix provides a guide for choosing between standard Rust idioms and Rustica's domain types. See §2 for why each anti-pattern was retired.

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
| Structural sharing | Full clone (`Vec::clone`) | `Arc<Vec<T>>` or `imbl::Vector` | `PersistentVector<T>` *(deprecated in 0.18.0, removal in 0.19.0)* |
| Nested struct updates | Manual clone-and-assign | In-place mutable setters | `Lens::set`, `Lens::then` |
| Deep enum branching | Nested `match` blocks | `if let` matching | `Prism::preview`, `Prism::then` |

---

## 5. Summary

Rustica embraces Rust's native model over emulating foreign paradigms. Delegating state, side effects, and control flow to the borrow checker, affine types, and native operators eliminates unnecessary indirection for most codebases, trading off the compositional flexibility that effect monads offer to interpreter- or effect-heavy architectures (§2.6).

The result is a zero-cost, idiom-aligned library targeting functional problems that the standard library leaves unsolved.
