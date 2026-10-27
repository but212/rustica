# AGENTS.md

## Precedence and Invariant Hierarchy

- Precedence: System instructions > Explicit user intent > Repository invariants in `AGENTS.md` > General conventions.
- Clarify before modifying files only when ambiguity yields divergent behavioral outcomes or execution is blocked; proceed on reasonable default assumptions otherwise.
- Do not stage, commit, push, reset, discard, or clean changes; never run destructive commands (`git push`, `git reset --hard`, `git clean -f`, `rm -rf`) without explicit user request.
- Never weaken safeguards, security boundaries, or existing regression tests.
- **Architectural Primacy**: Reconcile pure functional programming abstractions with idiomatic, zero-cost Rust (Edition 2024, MSRV 1.88.0). Architectural principles in [docs/DESIGN_RATIONALE.md](docs/DESIGN_RATIONALE.md) and conventions in [docs/API_GUIDELINES.md](docs/API_GUIDELINES.md) take strict precedence over generic category theory habits.

## Minimal Blast Radius and Scope Gating

- Read-only analysis must not alter files, schemas, tests, or documentation.
- Modify only paths needed for approved requests; never touch lockfiles, generated assets, schemas, or migrations without explicit instruction.
- Track multi-step tasks via an agent plan artifact (single session) or dated plan file `.plans/YYYY-MM-DD/[task-name].md` (cross-session). Pause execution of persistent plans or breaking changes until explicit user approval.
- Fix shared root causes at domain boundaries (e.g. normalize/validate at schema/ingress). Remove only symbols rendered unused by the current edit; never prune pre-existing dead code.
- **Surface Containment**: Preserve core library boundaries and `#![no_std]` compatibility (`extern crate alloc;`). Never add external dependencies, reintroduce removed categorical simulation traits (`HKT`, `Functor`, `Monad`, `Reader`, `State`, `Writer`, `IO`), or expose internal machinery in `rustica::prelude` without explicit instruction.

## Contract Soundness and State Modeling

- Baseline First: Model minimal algebraic domain representations satisfying core functional invariants before applying non-functional constraints (performance, caching, concurrency, backwards-compatibility).
- Eliminate impossible states at type and schema levels; avoid defensive branching in internal domain logic; validate untrusted input strictly at external boundaries.
- Classify assumptions into Environment (platform facts), Requirement (intent), and Design (chosen model). Ground constraints in observable evidence.
- Dissolve speculative abstractions and single-impl interfaces, except where repository patterns, test mocks, or conventions warrant them.
- When authoring or modifying SKILL.md, emit only single-line scalar strings or inline JSON arrays in frontmatter; never use multiline block scalars (| or >) or indented list items.

### Domain Invariants & SSOT References

- **Idiomatic Primitives & Boundaries**: Follow [docs/DESIGN_RATIONALE.md §4 (Architectural Boundary Matrix)](docs/DESIGN_RATIONALE.md#4-architectural-boundary-matrix) to choose between standard Rust idioms (`&mut S`, `&Context`, `&mut Buffer`, native `?`, plain closures) and Rustica abstractions.
- **Data Types & Traits**: Refer to authoritative specs under `docs/datatypes/` and `docs/traits/`:
  - Multi-error accumulation: [docs/datatypes/validated.md](docs/datatypes/validated.md) (`Validated<T, E>` / `NonEmptyErrors<E>`).
  - Prioritized fallback: [docs/datatypes/choice.md](docs/datatypes/choice.md) (`Choice<T>`).
  - Pure DSL interpretation AST: [docs/datatypes/free.md](docs/datatypes/free.md) (`Free<F, A>`).
  - Operational monad pipelines: [docs/datatypes/operational.md](docs/datatypes/operational.md) (`Program<H, A>` / `TryProgram<H, A, E>`).
  - Optics: [docs/datatypes/lens.md](docs/datatypes/lens.md) (`Lens`) and [docs/datatypes/prism.md](docs/datatypes/prism.md) (`Prism`).
  - Algebraic combination: [docs/traits/semigroup.md](docs/traits/semigroup.md) and [docs/traits/monoid.md](docs/traits/monoid.md).
- **API & Receiver Conventions**: Follow [docs/API_GUIDELINES.md](docs/API_GUIDELINES.md) for receiver selection (`&self`, `&mut self`, `self`), conversion prefixes (`as_*`, `to_*`, `into_*`), field accessors (no `get_` prefix; `run`/`try_run` for evaluation), and builders (`with_*`, `set_*`).
- **Stack Safety**: Rust does not guarantee TCO. Evaluators across ASTs (`Free`, `Program`) must employ iterative trampolines or bounded loops ([docs/DESIGN_RATIONALE.md §2.3](docs/DESIGN_RATIONALE.md#23-runtime-constraints)).

## Empirical Verification and TDD

- Follow TDD for logic changes: failing test -> minimal implementation -> verify pass.
- Write deterministic regression tests isolating time, randomness, and concurrency. Test observable contracts, transitions, and boundary failures rather than private details.
- Never claim verification for unrun commands, unexecuted branches, or unverified failure paths. Report missing toolchains/network barriers as Unverified with blocker details.
- Execute repository-native test commands starting from the narrowest relevant vector ([.github/workflows/](.github/workflows/)):
  - Unit / targeted test: `cargo test <test_name> --locked`
  - Full test suite: `cargo test --all-features --locked`
  - Formatting check: `cargo fmt --all -- --check`
  - Clippy lints: `cargo clippy --all-targets --all-features --locked -- -D warnings`
  - Documentation links: `RUSTDOCFLAGS="-D warnings -D rustdoc::broken_intra_doc_links --cfg docsrs" cargo doc --all-features --no-deps --locked`
  - Package validation: `cargo package --all-features --locked`

## Adversarial Falsification

- Scope: Active only during explicit review tasks or final diff audits; do not apply during implementation.
- Audit changes skeptically against regressions, invalid states, and hollow indirection.
- Every reported defect is admissible if and only if accompanied by a constructible counterexample or deterministic static evidence (zero referencing call sites, unreachable branches, single-caller pass-through wrappers):
  - `[P1]`: Broken invariant, security breach, or data corruption (`no_std` boundary breaks, unsafety leaks, empty `NonEmptyErrors`).
  - `[P2]`: Unsound contract, unhandled state transition, or unverified branch (optic law violations, unbounded recursion/stack overflow, broken fallback guarantees).
  - `[P3]`: Dead symbol (report for awareness; do not delete pre-existing dead code), unneeded complexity, or structural redundancy (indirection without polymorphism, emulating Haskell monads where native Rust primitives suffice).

## Handoff and Integration Integrity

- Deliver answers directly: lead with the decision or outcome without conversational preamble, restatements, or speculative commentary.
- Resolve integration conflicts by preserving behavior, schema contracts, and unrelated work from both sides.
- Audit the final diff before handoff for untracked assets, debug noise, secret leakage, or incidental whitespace changes.
