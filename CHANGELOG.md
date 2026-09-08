# CHANGELOG

## [0.16.0]

### Priority & Fallback Semantics (`Choice<T>`)

- **Semantic Fallback Execution**: Added `Choice::try_each`, `Choice::try_each_validated`, and `Choice::first_match` fallback execution primitives.
- **Error Accumulation Synergy**: `Choice::try_each_validated` accumulates errors across all alternatives into `Validated<E, R>` upon total failure.
- **Category-Theory Deprecations**: Deprecated `Choice::bind`, `Choice::apply`, and `Pure`, `Applicative`, and `Monad` implementations for `Choice<T>` to align with priority/fallback semantics.
- **Documentation Overhaul**: Updated `Choice<T>` rustdoc with primary/fallback domain guidance and runnable doctests.

### Bug Fixes & Soundness

- **AsRef Panic Removal**: Removed panicking `AsRef` implementations from `First` and `Last` in favor of non-panicking `get()` and `into_value()`.
- **IO::delay Reactor Nesting**: Resolved Tokio thread panics caused by nested `block_on` runtime invocations in `IO::delay`.
- **PVec Reversal and Height Reset**: Fixed order reversal and height loss bugs in `pop_front_from_tree` within `src/pvec/tree.rs`.
- **PVec Single-Pass Tree Pop**: Optimized `pop_from_tree` in `src/pvec/tree.rs` to consume popped values directly from `root.pop_back()`, removing redundant $O(\log n)$ tree lookups and duplicate clones.
- **PVec Structural Sharing in `Extend`**: Preserved structural sharing in `Extend::extend` via amortized $O(1)$ tail pushes (`push_back`), eliminating full-vector heap reallocations and tree rebuilds.
- **PVec Debug Trait Bound & Formatting**: Relaxed `Debug` bound on `PersistentVector<T>` from `T: Clone + Debug` to `T: Debug`, enabling non-clone element formatting and standardizing output to list format (`[...]`).
- **PVec Invariants & Inline Fast-Paths**: Enforced uniform branch height in `concat_nodes` via `unreachable!`, and added direct in-place `SmallVec` fast-paths for `insert` and `remove` on `Inline` vectors ($\le 64$ elements).
- **Vec Alternative Monoidal Semantics**: Changed `<Vec<T> as Alternative>::alt` from first-non-empty semantics to monoidal concatenation (`self.extend(other)`).

### Free Monad (`Free<F, A>`)

- Added `Free<F, A>` to separate program description from execution.
- Renamed internal AST variants to `Free::Suspend` and `Free::Bind`, aligning with `Monad::bind` trait conventions.
- Standardized effect constructor to `Free::suspend` (removed `lift_f`), and provided `is_suspend` and `is_bind` state predicates.
- Evaluated left-associated chains iteratively in `run` and `try_run` to prevent stack overflows.
- Added `FreeError<E>` to handle interpreter errors and downcast mismatches without panicking in `try_run`.
- Made `Drop` and `fmt::Debug` iterative to prevent stack overflows on deep trees.
- Added `Free::fold_map` to convert a `Free` program into `IO<A>`.

### Operational Monad (`Program<H, A>`, `TryProgram<H, A, E>`)

- Added statically-typed operational monads in `rustica::datatypes::operational` (`Program`, `TryProgram`).
- Bound each `Command` to its exact output type (`Command::Output`), enforcing 100% compile-time type safety on interpreter handlers (`Handler<C>`, `TryHandler<C, E>`) with zero dynamic downcasting (`AnyValue`).
- Unified execution engine on `TryProgram` with `Program` providing a zero-cost infallible wrapper.
- Implemented stack-safe trampoline execution (`run`, `try_run`) and custom iterative `Drop` preventing stack overflows on deep un-evaluated chains.
- Added constructor extension methods on `Command` (`cmd.suspend::<H>()`, `cmd.try_suspend::<H, E>()`) and freestanding helpers (`operational::suspend`, `operational::try_suspend`).
- Re-exported `Command`, `Handler`, `Program`, `TryHandler`, and `TryProgram` in `rustica::prelude::datatypes`.

### Trait Bounds & Structural Cleanup

- **Feature Flag Isolation (`pvec`)**: Gated `PersistentVector` behind the optional `pvec` Cargo feature flag (disabled by default, included in `full` and `develop`) to minimize baseline compile times and dependencies.
- **Over-Constrained Bounds Relaxed**: Removed unnecessary `E: Debug`, `E: Clone`, and `S: Default` bounds from `Result`, `State`, and `PersistentVector`.
- **Applicative Polarity Rectified**: Inverted `apply` argument polarity on `ContT` and `ReaderT` (`fn.apply(val)`) to match standard functional programming Applicative conventions.
- **Rust API Guidelines Receiver Alignment**: Aligned method receivers with official Rust API Guidelines (C-CONV, C-BUILDER, C-GETTER). Renamed consuming conversions to `into_*` (`StateT::into_state`, `ContT::into_cont`, `WithError::into_result`), builder method to `with_error_code`, and consuming execution runners to `IO::try_run*`. Converted `Writer::log` from consuming to borrowed `&self` (breaking; use `Writer::into_log(self)` to consume). Converted `Choice::flatten` and `Choice::try_flatten` from borrowed `&self` to consuming `self` (breaking; eliminates `T: Clone` requirement; use `.clone().flatten()` or `flatten_cloned` for borrows). Added consuming `Choice::filter`.
- **Prelude Exports**: Added missing prelude exports for `BinaryHKT`, `ChoiceError`, `ValidatedError`, `Free`, `FreeError`, and the `context!` macro.
- **Ergonomic Aliases**: Added `Id::get`, `Id::into_value`, `into_value` on wrappers (`First`, `Last`, `Min`, `Max`, `Product`, `Sum`), `eval` on `Predicate`, `single` on `PersistentVector`, and `AsyncM::join`.

### Deprecations (Planned for Removal in 0.17.0)

- **`Iso` Family**: Deprecated `Iso`, `IsoExt`, `ComposedIso`, `InverseIso`, and `ResultValidatedIso` in favor of standard `From`/`Into` and `TryFrom`/`TryInto`.
- **`Bifunctor`**: Deprecated `Bifunctor` trait in favor of inherent `bimap`/`first`/`second` methods and standard Rust pattern matching.
- **`FoldableExt` Search Methods**: Deprecated non-short-circuiting linear traversal methods on `FoldableExt` (`find`, `all`, `any`, `contains`, `is_sorted`) in favor of Rust's standard `Iterator` equivalents.
- **`Alternative::many`**: Deprecated `Alternative::many` in favor of standard iterator combinators or explicit repetition.
- **`FunctorExt` Combinators**: Deprecated `filter_map`, `try_map_or`, and `try_map_or_else` on `FunctorExt` in favor of standard `Iterator::filter_map` or `fmap` with `unwrap_or`/`unwrap_or_else`.
- **`PureExt` Combinators**: Deprecated `pair_with`, `lift_other`, and `combine_with` on `PureExt` in favor of direct value construction and `Pure::pure`.
- **`Monad` Methods**: Deprecated `map_and_pure` and `try_bind` on `Monad` in favor of `Functor::fmap` or explicit error handling inside `bind`.
- **`SemigroupExt` / Helpers**: Deprecated `SemigroupExt::combine_all`, `combine_n` and standalone functions `combine_all_values`, `combine_values` in favor of standard iterator folds with `combine`.
- **`MonoidExt` / Helpers**: Deprecated `MonoidExt::is_empty_monoid`, `monoid::mconcat`, and `monoid::power` in favor of comparison with `Monoid::empty()`, `monoid::combine_all`, and `monoid::repeat`.
- **Type Construction & Accessor Renames**:
  - Deprecated `PersistentVector::unit` in favor of `PersistentVector::single`.
  - Deprecated `Choice::first` in favor of `Choice::primary`.
  - Deprecated `StateT::to_state` in favor of `StateT::into_state` (C-CONV).
  - Deprecated `ContT::to_cont` in favor of `ContT::into_cont` (C-CONV).
  - Deprecated `WithError::to_result` in favor of `WithError::into_result` (C-CONV).
  - Deprecated `ComposableError::set_code` in favor of `ComposableError::with_error_code` (C-BUILDER).
  - Deprecated `IO::try_get*` runner family in favor of `IO::try_run*` (C-GETTER).
  - Deprecated `Choice::filter_values` in favor of consuming `Choice::filter`.
  - Deprecated `Validated::errors` in favor of `Validated::error_slice` or `iter_errors`.
  - Deprecated `ComposableError<E>` in favor of `ContextError<E>` (scheduled for removal in 0.18.0).
  - Deprecated `ComposableResult<T, E>` in favor of standard `Result<T, ContextError<E>>` (scheduled for removal in 0.18.0).
  - Deprecated `BoxedComposableError<E>` and `BoxedComposableResult<T, E>` in favor of standard `Result<T, Box<ContextError<E>>>` (scheduled for removal in 0.18.0).
  - Deprecated `WithError<E>` and `sequence_with_error` in favor of standard `Result` combinators and `Iterator::collect` (scheduled for removal in 0.18.0).
  - Deprecated `IO::run_async` in favor of runtime task spawning APIs (scheduled for removal in 0.18.0).

### Error System Slimdown

- **Standard Rust Result & Error First**: Adopted `Result<T, E>` and `std::error::Error` as primary error primitives.
- **Introduced `ContextError<E>`**: A minimal context accumulation wrapper replacing `ComposableError<E>` without HKT, `SmallVec`, or application-specific error code metadata.
- **Context API Updates**: `with_context_result` returns standard `Result<T, ContextError<E>>` directly. Preserved lazy context evaluation via `context!` macro and `accumulate_context`.
- **Modernized Effect Runners**: `IO::try_run*`, `State::try_*_state*`, `StateT::try_*_state*`, and `ReaderT::try_run_reader*` return standard `Result` and provide `_context` methods for attaching context, deprecating old composable error runner variants.

### Async Primitives & Dependency Decoupling

- **Eliminated `futures` Dependency**: Removed `futures` and sub-crates from production dependencies; `AsyncM` and `Validated` async combinators now use standard library async primitives (`std::future::Future`, `Box::pin`, `std::panic::catch_unwind`).
- **Executor-Agnostic Core Async**: Replaced `tokio::join!` in `AsyncM::apply` and `AsyncM::zip_with` with a zero-dependency, cooperative standard future join (`Join2`).
- **Sequential Error Mapping**: `Validated::fmap_invalid_async` now executes error transformations sequentially without external concurrency dependencies.
- **`IO::run_async` Deprecation**: Deprecated `IO::run_async` (scheduled for removal in 0.18.0). Tokio production dependency is trimmed to `rt` feature only for this method.
- **NOTICE Cleanup**: Removed obsolete third-party entries (`futures`, `rayon`, `lazy_static`) from `NOTICE`.

## [0.15.0]

### Bug Fixes

- **IO::delay Tokio Reactor Panic**: Fixed `IO::delay` to construct `tokio::time::sleep` inside an `async` block evaluated by `TOKIO_RUNTIME.block_on`, eliminating reactor panics outside an active Tokio runtime.
- **PVec Uniform-Height Tree Invariant**: Implemented recursive, height-aware front and back leaf insertion (`push_front_leaf_recursive`, `push_back_leaf_recursive`) and height-aligned concatenation in `RRBTree`, eliminating depth corruption and data loss on height $\ge 2$ trees.
- **PVec Index Routing**: Fixed capacity calculation in `calculate_adjusted_index` to properly scale by tree height (`LEAF_CAPACITY * BRANCHING_FACTOR.pow(height)`), preventing tree corruption for vectors with >2048 elements.
- **PVec Branch Traversal**: Made `RRBNode::update` height-aware using relaxed/regular branch navigation; deleted height-blind `find_child` and dead `RRBNode::get`; routed `pop_from_tree` to `get_from_tree`.
- **Differential QuickCheck Suite**: Added `tests/pvec_differential.rs` verifying arbitrary sequences of `push`, `pop`, `update`, `split_at`, and `concat` against `std::vec::Vec`.
- **Validated Panic Context**: `unwrap()` and `unwrap_invalid()` now preserve and format inner error and success payloads in panic messages.
- **Trait Generic Bounds**: Aligned `Fn` and `Clone` bounds between trait declarations and implementations for `Functor` and `Monad` across `Vec`, `Option`, and `Result`.

### Contract Integrity & Laws

- **Receiver Unification & Move Semantics**:
  - Consolidated dual borrowed/owned APIs into unified owned `self` signatures (`foo(self)`).
  - Deprecated `*_owned` variants on core effect types (`IO::run_owned`, `IO::run_async_owned`, `Writer::run_owned`, `Writer::unwrap_owned`, `State::run_state_owned`, `State::eval_state_owned`, `State::exec_state_owned`, `Reader::run_reader_owned`, `Validated::unwrap_owned`, `Validated::unwrap_invalid_owned`, `Validated::combine_errors_owned`, `Validated::sequence_owned`, `Validated::collect_owned`, `Validated::from_option_owned`, `Validated::from_option_with_owned`, `Validated::fmap_invalid_owned`, `MonadError::catch_owned`), forwarding to unified counterparts.
  - Generalized `Alternative::alt`, `Alternative::many`, `Bifunctor` methods (`first`, `second`, `bimap`), `StateT`, `ReaderT`, and `Validated` methods (`combine_errors`, `fmap_invalid`, `sequence`, `unwrap`, `unwrap_invalid`, `unwrap_or`, and async methods) to owned receivers, eliminating spurious `Clone` bounds.
  - Generalized `Foldable::fold_left` and `fold_right` to consume the accumulator by value, enabling zero-copy folding over non-`Clone` accumulators (`U: !Clone`).
  - Generalized `Iso::forward` and `backward` to accept values by move.
  - Effect types: `IO::run(self)` and `IO::run_async(self)` support move-only types; `State::run_state(self, s)`, `eval_state`, `exec_state`, `Reader::run_reader(self, env)`, `Writer::run(self)`, and `into_value(self)` consume `self`.
  - Stripped unnecessary `Clone` bounds from `Functor::fmap` result type `B`, `Monad::bind` target type `U`, and `IO::run`/`Writer::unwrap` output types.
- **Validated Semigroup Accumulation**: `Validated<E, A>: Semigroup` now requires `A: Semigroup` and accumulates valid components `(Valid(a1), Valid(a2)) => Valid(a1.combine(a2))`, with errors taking precedence. `Alternative` is omitted because `NonEmptyErrors` lacks an empty identity element.
- **Product Monoid Law**: Introduced `One` trait (`rustica::traits::one::One`) implemented for all numeric primitives (`u8`..`u128`, `usize`, `i8`..`i128`, `isize`, `f32`, `f64`), enabling `Product<i8>: Monoid`.
- **IO Cold Computation**: Eliminated `IO::new_async` cold-computation caching bug; made `IO::delay` instantiate fresh sleep operations per run. Pure `fmap`, `bind`, and `apply` paths defer callbacks until each run (always producing `Effect` representation).
- **AsyncM Cold Computation**: Pure `apply` and `zip_with` paths defer callbacks until each `try_get` evaluation and remain repeatable.
- **Choice Flattening**: `Choice::flatten` returns `Option<Choice<I>>` instead of panicking on empty iterators.
- **Prelude Exports**: Re-exported `compose` macro in `prelude::category` and `lift` function in `prelude::transformers`.
- **BinaryHKT Separation**: Removed runtime mapping methods `map_second` and `map_second_owned` from `BinaryHKT` to preserve pure type-constructor boundaries.

### Structural Pruning & Cleanup

- **Wrapper & Value Accessors**: Added idiomatic `into_inner()` and `get()` accessors across wrapper types (`Sum`, `Product`, `Min`, `Max`, `First`, `Last`), deprecating `unwrap()` and `unwrap_or()`; added `into_value()` on `Writer`, deprecating `unwrap()`; deprecated `Thunk` in favor of closures; removed unused `A: Debug` bound from `IO::sequence_composable`.
- **Transformer Simplification**: Removed manual `*_with` forwarding combinators (`fmap_with`, `bind_with`, `combine_with`, `apply_with`) from `StateT` and `ReaderT`; deprecated `ReaderT::unwrap_with` in favor of `run_reader`; made `ReaderT::lift2` an associated function.
- **Hollow Traits Deprecation**: Deprecated `MonadPlus` (migrated to `Alternative`) and `ErrorMapper` (migrated to `Result::map_err` / `Option::ok_or`).
- **Applicative / Bifunctor / Foldable**: Deprecated `Applicative::ap2` in favor of `lift2`; added default implementations for `Bifunctor::first` and `second` via `bimap`; simplified `Monad::map_and_pure` to delegate to `fmap`; simplified `Foldable::fold_monoid` to delegate to `fold_map`.
- **PVec Optimization**: Replaced $O(n \log n)$ shared-tree fallback in `into_vec` with $O(n)$ iterator collect; generalized `update_size_table_after_removal`; bounded concatenation branches to 32 children while preserving structural sharing.
- **Optics & Predicate**: Replaced `IsoLens`/`IsoPrism` with `Lens::from_iso`/`Prism::from_iso`; deprecated `compose` on `Lens` and `Prism` in favor of `then`; stored thread-safe closures in `Predicate` via `Arc`.
- **Redundant API Removal & Deprecation**: Removed `FunctionCategory::lift` in favor of `FunctionCategory::arrow`; deprecated `Id::unwrap`, `Id::unwrap_or`, and `Writer::exec` in favor of `Id::into_inner` and `Writer::log`.
- **Utils Deprecation**: Deprecated `rustica::utils` module and its helpers (`pipeline_option`, `pipeline_result`, `transform_chain`) in favor of standard `Iterator::try_fold` and `Option::map` / `Functor::fmap`.

## [0.14.0]

### Documentation Correctness

- Documented `Min<T>` and `Max<T>` as `Semigroup` wrappers without a generic `Monoid` identity. Use `semigroup::combine_all_values` for empty-capable reductions or provide a domain-specific extremum.

### Bug Fixes

- Fixed `PersistentVector::concat` ordering across unequal-height RRB trees.
- Fixed `PersistentVector::pop_back` to drain the front head buffer after the tree is exhausted.

### Tests

- Added regressions for unequal-height `PersistentVector::concat`, full head/tree `pop_back` draining, and `FoldableExt::fold_option` short-circuiting.
- Added compile-fail contracts for removed unlawful implementations and phantom marker wrappers.

### Changed

- Generalized `pipeline_result` from `Vec<Func>` to any `IntoIterator<Item = Func>`, matching `pipeline_option`.

### CI/CD and Security

- Added least-privilege workflow permissions, pinned external actions, and `actionlint`/`zizmor` checks.
- Declared MSRV through `package.rust-version` with a dedicated CI check.
- Hardened releases with locked packaging, exact CHANGELOG validation, a protected crates.io environment, and verified SLSA verifier downloads.
- Added trusted benchmark regression reporting with a 20% slowdown threshold.
- Added repository ownership, security reporting, pull-request, and issue templates under `.github/`.

### Breaking Changes

- **Lawful Algebraic Trait Surface**:
  - Removed `Monoid` for `Min<T>`/`Max<T>`; use `Semigroup::combine` with an explicit extremum or `combine_all_values` for empty-capable reductions.
  - Removed `MonadPlus` for `Result<T, E>` because arbitrary `E` has no lawful zero; use `Result::or_else`.
  - Removed unused `HKTType`/`PureType` phantom wrappers; use `HKT`, `Pure`, or `PureExt`.
- **Transformer State and Type Invariants**:
  - `ReaderT<E, M, A>` requires `M: HKT<Source = A>`; type-changing operations return `M::Output<B>`, and the unsafe bind conversion was removed.
  - `StateT<S, M, A>` has one executable representation, requires `M: HKT<Source = (S, A)>`, and threads state left-to-right.
  - `StateT` no longer exposes `Pure` or `LiftM`; `MonadTransformer::BaseMonad` is the base family containing `A`, not `(S, A)`.
- **Error and Conversion API**:
  - Removed impossible `ChoiceError::EmptyChoice`, `PVecError::InvalidRange`, and `IOError::ValueNotSet` variants.
  - Removed `ErrorOps`, `sequence`, `traverse`, and redundant free error-conversion functions; use `Result`/`Iterator` methods and `From`.
  - `Validated` converts from owned or borrowed `Result` through `From`; lossy conversion is `into_result_first_error`.
  - Replaced panicking `NonEmptyErrors` `FromIterator` with `NonEmptyErrors::try_from_iter`, returning `Option` for empty-capable input.
  - Removed panicking `Choice` conversions from `Vec`, slices, and iterators. Use `Choice::of_many` for `Option` or `TryFrom` for `Result<Choice<T>, ChoiceError>`; empty input returns `ChoiceError::EmptyInput`.
- **Dead Utilities Removed**:
  - Removed empty `utils::categorical_utils`, the `utils::functions::id` alias, and unused `ReaderCombineFn`/`ContFn` aliases.
- **Duplicate Functional Data Types Removed**:
  - Removed `Maybe<T>` in favor of standard `Option<T>`.
  - Removed `Either<L, R>`, `EitherError`, `ResultEitherIso`, and `Either` conversion helpers in favor of `Result<R, L>` or the external `either` crate.
- **Single-Implementation Traits Removed**:
  - Removed `Category`/`Arrow`; `FunctionCategory` exposes morphism operations as inherent associated functions: `identity_morphism`, `compose_morphisms`, `arrow`, `first`, `second`, `split`, and `combine_morphisms`. `function!`, `compose!`, and `pipe!` no longer require trait imports.
  - Removed `Comonad`; `Id<T>` provides `extract`, `duplicate`, and `extend` inherently.
  - Removed `Evaluate`/`EvaluateExt`; `Thunk` and `IO` expose `Thunk::evaluate` and `IO::run` inherently.
- **Redundant Wrappers & Pipelines Removed**:
  - Removed `ErrorPipeline`/`error_pipeline` in favor of standard `Result` combinators, `ErrorCategory` in favor of `Result`/`Validated`, `Pipeline<T>` from `rustica::utils::transform_utils`, and `Memoizer` in favor of dedicated caching crates (`lru`, `moka`).
- **Collection Iterator Helpers Removed**:
  - Removed `PersistentVector::take`/`skip`; use iterator adapters or `PersistentVector::split_at`.

### Maintenance

- Added central compile-fail removal contract doctests in `src/lib.rs`.
- Updated all doc examples and benchmarks to the 0.14.0 API.
- Persistent vectors derive length from their representation and compare/hash by logical element sequence; removed the unused generation counter.
- Added a targeted Miri CI test for owning `ReaderT::bind` values, removed redundant phantom fields, and removed the unused futures `thread-pool` feature.

## [0.13.0]

### Maintenance

- Relaxed owned error-conversion helpers to accept non-`Clone` values and simplified `Result` sequencing/pipelines with iterator combinators.
- Kept `ErrorPipeline` behavior unchanged; migrate to native `Result` combinators before its planned 0.14.0 removal.

### Breaking Changes

- **`Choice<T>` Impossible-State Elimination**:
  - Redesigned `Choice<T>` as `{ primary: T, alternatives: SmallVec<[T; 7]> }`, making empty choices impossible at compile time. `first()` returns `&T`; removed `new_empty()`; added `single()`, `of_many()` (`Option<Choice<T>>`), and `filter_values()`.
  - Implemented `Pure`, `Functor`, `Applicative`, `Monad`, `Semigroup`, `IntoIterator`, and `Foldable` for `Choice<T>`.
- **`NonEmptyErrors<E>` Invariant Preservation**:
  - Removed `NonEmptyErrors::remove()` so error collections cannot become empty.
- **Dead Code and Speculative Helpers Removed**:
  - Removed 0-impl `Traversable` trait and dead utilities: `const_fn`, `compose`, `pipe`, `flip`, `fold_with`, `bimap_result`, `fan_out`, `compose_all`, `lift_option`, and `transform_all`.
  - Re-exported `id` directly from `std::convert::identity`.
- **Deprecations (0.14.0 Removal Notice)**:
  - Deprecated `Maybe<T>` (use `Option<T>`), `Either<L, R>` (use `Result<R, L>` or `either`), one-implementation traits (`Comonad`, `Arrow`, `Category`, `Evaluate`, `EvaluateExt`), speculative wrappers (`ErrorCategory`, `ErrorPipeline`, `Pipeline<T>`, `Memoizer`), and `PersistentVector::{take, skip}`.
- **`Validated<E, A>` Non-Empty Error Invariant**:
  - `Invalid` stores `NonEmptyErrors<E>`; `invalid_many` rejects empty input, while `try_invalid_many` supports it. Serde rejects empty invalid arrays without changing the JSON representation. Removed `invalid_vec` and `error_buffer_mut`.
- **Legacy and Redundant APIs Removed**:
  - Removed legacy `Choice` mutation/iteration helpers, `PersistentVector` cache-policy constructors, `ResultExt`, `try_pipeline`, `compose_when`, stdlib-equivalent categorical collection helpers, `SemigroupExtAdapter`, and `combine_all_owned`.
- **Semigroup Repetition Contract**:
  - `SemigroupExt::combine_n` and `combine_n_owned` require `NonZeroUsize`, eliminating zero-count states.

### Changed

- Eliminated redundant clones across all targets; strict `clippy::redundant_clone` passes. `FoldableExt::to_vec` appends into one accumulator ($O(n)$, formerly $O(n^2)$).
- `PersistentVector` builds owned trees leaf-by-leaf, shares one recursive builder, and moves uniquely owned leaves during consuming conversion. Vec/Choice applicatives write directly to final collections; error display and owned panic payloads avoid clones.
- `ReaderT`/`StateT` callback adapters borrow `dyn Fn` callbacks; `ReaderT::lift2` returns an opaque callable. Memoizer insertion uses move replacement, named `InsertOutcome`, and limits `V: Clone` to owned-copy APIs; zero-capacity caches stay disabled.
- Validated paths share an `ErrorAccumulator` while preserving error order/accumulation; `traverse_validated` no longer requires `E: Clone`.
- Single-value `Either`/`Validated` iterators use `Option::IntoIter`; Tokio uses `std::sync::LazyLock`; `rayon`/`lazy_static` removed from runtime dependencies, `quickcheck` is optional, and `serde_json` is dev-only.

### Fixed

- Fixed owned semigroup repetition that duplicated accumulated values and owned `Validated` conversion that mishandled singleton errors.

See [MIGRATION_v0.13.0.md](MIGRATION_v0.13.0.md) for migration details.

## [0.12.0]

### Breaking Changes

- **`Choice<T>` Typeclass Cleanup**: Removed deprecated methods and functions.

## [0.11.1]

### Added

- **`Lens<S, A>` Composition**: Added `compose()` and fluent `then()` for type-safe nested lens access (e.g. `address_lens.compose(street_lens)`).
- **`Prism<S, A>` Composition**: Added `compose()` and fluent `then()` for type-safe nested sum-type access (e.g. `outer_prism.compose(inner_prism)`).

### Performance Optimizations

- **`Validated<E, A>` SmallVec Capacity**: Changed inline error storage from `SmallVec<[E; 8]>` to `[E; 4]`, halving stack usage while preserving common-case performance.

### Fixed

- **Memoizer Zero Capacity**: `Memoizer::with_capacity(0)` creates a disabled cache instead of an unbounded one.

## [0.11.0]

### Breaking Changes

- **`utils::hkt_utils::map_result` Consolidated**: Consolidated into `categorical_utils` (which accepts `FnOnce` instead of `Fn`); `hkt_utils::map_result` remains a backward-compatible re-export.
- **`Validated<E, A>` Typeclass Cleanup**: Removed `Monoid` (no lawful identity for accumulation), `AsRef<A>` (panicked on `Invalid`), `MonadPlus`, and `Alternative`; use `Validated::valid(...)`, `Validated::as_ref()`/pattern matching, or `recover_all`, `recover_all_at_once`, and `sequence_owned`.
- **`Either<L, R>` Typeclass Cleanup**: Removed `MonadPlus`; use `Alternative` for choice semantics.
- **`Choice<T>` Typeclass Cleanup**: Removed duplicate `MonadPlus`; migrate `mzero()` → `Alternative::empty_alt()` and `mplus()` → `alt()`. `Foldable` no longer requires `T: Clone`.
- **`utils::error_utils` Module Relocated**: Moved `WithError`, `ResultExt`, `sequence`, `traverse`, and related utilities to `crate::error`; migrate imports to `rustica::error::*` or `rustica::prelude::error::*`.
- **Identity Trait Removed**: Removed deprecated `Identity` and `traits::identity`, including implementations for `Id`, `Maybe`, `Either`, `Validated`, `Choice`, `PersistentVector`, `First`, `Last`, `Max`, `Min`, `Product`, `Sum`, and `Writer`.
- **Legacy `AppError` Utilities Removed**: Removed `AppError`, `error()`, and `error_with_context()`; route error construction through `crate::error::ComposableError` and context helpers.

### Changed

- **Core Error Helper Cleanup**: `Either::to_result` / `from_result` delegate to `crate::error::{either_to_result, result_to_either}`. `IO::try_get`, `IO::try_get_with_context`, and `Maybe::try_unwrap` return `ComposableResult`.
- **Error Prelude Consolidation**: `prelude::error` re-exports unified error module: `ComposableError`, `ComposableResult`, boxed variants, context utilities, `WithError`, `ResultExt`.
- **`Choice<T>` Clarifications & Signatures**: Documented that `Semigroup::combine` and `Alternative::alt` share the same "merge alternatives" behavior. `flatten()` panics on empty primary iterators (use `try_flatten()` for safe alternative). `try_remove_alternative()`, `try_flatten()`, and `try_swap_with_alternative()` return `Result<_, ChoiceError>`; added non-panicking `try_first()`.
- **Safe Extraction Methods Added**:
  - `Either<L, R>`: Added `try_unwrap_left()`, `try_unwrap_right()`, `try_left_ref()`, and `try_right_ref()`, returning `Result<_, EitherError>`.
  - `Validated<E, A>`: Added `try_unwrap()`, `try_unwrap_invalid()`, and `try_valid_ref()`, returning `Result<_, ValidatedError>`.
- **New Structured Error Types**: Added `ChoiceError` (`NoAlternatives`, `IndexOutOfBounds`, `EmptyPrimaryIterator`, `EmptyChoice`), `EitherError` (`ExpectedLeft`, `ExpectedRight`), and `ValidatedError` (`ExpectedValid`, `ExpectedInvalid`) in `datatypes::error`.
- **Unused Placeholder Modules Removed**: Removed `contravariant_functor`, `natural_transformation`, `profunctor`, and `representable`.
- **`Validated<E, A>` Optimizations**: Aligned `iter_errors()` with `iter_errors_mut()` using `ErrorsIter`; `collect()`/`collect_owned()` require only `C: FromIterator<A>`; direct `extend()` removes iterator overhead; added zero-copy `as_option()`/`into_option()`; added async owned `fmap_valid_async_owned()`, `fmap_invalid_async_owned()`, and `and_then_async_owned()` using `FnOnce`.
- **`PersistentVector<T>` Optimizations**: Reduced full iteration from $O(n \log n)$ to $O(n)$ via stack traversal; `fold_right` uses `DoubleEndedIterator`; removed `T: Clone` requirement from `get()`, indexing, borrowed iteration, and `Foldable`; added bidirectional front/back cursors.
- **`Memoizer` Improvements**: Added bounded $O(1)$ LRU eviction via `with_capacity(max)`, statistics (`stats`, `hit_rate`, `reset_stats`, `max_capacity`), manual/fallible operations (`insert`/`try_insert`, `get_or_try_compute`, `touch`/`try_touch`), map methods (`len`, `contains_key`, `remove`, `get`, `reserve`, `shrink_to_fit`, `keys`, `values`, `capacity`, `clear` and fallible `try_*` variants for lock poisoning). Fixed optimistic computation and clarified `get()` vs `peek()` LRU semantics.

## [0.10.2]

### Deprecated

- **`Choice<T>` Utility Methods**: Deprecated until v0.12.0: `has_alternatives()` (use `!alternatives().is_empty()`), `to_vec()` (use `Into::<Vec<T>>::into()` or `.iter().cloned().collect()`), `find_first()` (use `iter().find()`), `dedup()`/`dedup_by_key()` (use external iteration), `fold()` (use `Foldable::fold_left`/`fold_right`), `to_map_with_key()` (use `iter().map().collect()`), `add_alternatives()` (use `Semigroup::combine()` or Monoid operations), `remove_alternative()`/`try_remove_alternative()` (use `filter_values()`), `filter()` (use `filter_values()`), `fmap_alternatives()` (use `fmap()` or external iteration), `flatten_sorted()` (use `flatten()` then sort), `iter_alternatives()` (use `alternatives().iter()`), `swap_with_alternative()`/`try_swap_with_alternative()` (use external patterns), and `bind_lazy()` (use `bind()` with `into_iter()` or `flat_map`).
- **Legacy Error Utilities (`utils::error_utils`)**: Deprecated in favor of `crate::error`: `result_to_either()` → `crate::error::result_to_either()`, `either_to_result()` → `crate::error::either_to_result()`, `ResultExt::to_validated()` → `crate::error::result_to_validated()`, `ResultExt::to_either()` → `crate::error::result_to_either()`, and `ResultExt::bimap()` → `crate::error::ErrorOps::bimap_result()`. Deprecated `AppError<M, C>` and `error()`/`error_with_context()` in favor of `ComposableError`.

### Breaking Changes

- **Composable Error Helpers**: `State`, `Maybe`, `IO`, `ReaderT`, and `StateT` `try_*` helpers return `ComposableResult`/`ComposableError`. Removed legacy types, constructors, and examples; migrate to `core_error()` and `context()`.
- **`src/error` Module API Changes**: Removed redundant `with_context_result_boxed()` in favor of `with_context_result()`. `ErrorPipeline::finish()` returns `Result<T, Box<ComposableError<E>>>` instead of `Result<T, ComposableError<E>>`.
- **`Validated` Error Handling**: Removed `ErrorOps` implementation due to accumulation conflict; use `recover_all` or `recover_all_at_once`.

### Changed

- **`Choice<T>` Categorical API Focus**: Retained essential Functor/Applicative/Monad/MonadPlus API (`new`, `new_empty`, `first`, `alternatives`, `len`, `is_empty`, `filter_values`, `flatten`, `try_flatten`, `of_many`, `iter`); deprecated auxiliary utility methods.
- **`Choice<T>` Memory Optimization**: Replaced `Arc<SmallVec<[T; 8]>>` with owned `SmallVec<[T; 8]>`, removing reference-counting overhead and broken `try_unwrap` paths while reducing small-choice memory by ~40%.
- **`AsyncM` Optimization**: Added Pure and Pure+Pure fast paths (including `apply`/`zip_with`), inlining, and `AsyncMInner` Pure/Lazy enum, reducing `Arc` cloning.
- **`IO` Applicative Signature & Optimization**:
  - **Breaking**: Changed `apply` to standard Applicative `IO<A>.apply(IO<Fn(A) -> B>) -> IO<B>`, removing former `bind` alias `IO<A>.apply(Fn(A) -> IO<B>)`.
  - Added Pure+Pure and mixed Pure/Effect fast paths, inlining, and optimized runners.
- **Error Performance**: Inline context matching and buffering in `SmallVec<[String; 4]>` in `src/error`; standardized context inputs on `Into<String>`.
- **`Validated` Accumulation Optimization**: Reusable `ErrorAccumulator` backed by `SmallVec<[E; 8]>`, owned `combine_errors_owned`/`sequence_owned`/`collect_owned` variants, zero-copy `error_slice`/`error_buffer_mut` accessors, and non-`Clone` iterators.

## [0.10.1]

### Breaking Changes

- **Identity Trait Deprecation**: Deprecated `Identity` in favor of `Functor` directly extending `HKT`; moved `id()` to `utils::functions` (scheduled for removal in v0.12.0; use `unwrap()`, `as_ref()`, or `Comonad::extract()`). Added `MIGRATION_v0.11.0.md`.

### Added

- Added `utils::functions::{id, const_fn}`.
- Documented `PersistentVector`, added `pipe` to `utils::transform_utils`, and added migration guide.
- Integrated `src/error` with `IO`: added `try_get_composable()`, `try_get_composable_with_context()`, `into_error_pipeline()`, `recover()`, `recover_with()`, and `sequence_composable()`. Full error chains and context are preserved through IO.

### Changed

- Updated `ComposableError` documentation, recovery guidance, and Quick Start examples.

### Fixed

- Category Theory Compliance: `Functor` extends only `HKT`, separating value extraction from functor operations.
- Fixed compose function order in tests.
- Fixed `map_error` doctests by removing problematic methods.

## [0.10.0]

### Added

- Added `From<T>`/`Into<T>` for `Sum<T>`, `Product<T>`, `Min<T>`, `Max<T>`, and `Value<T>`, plus `From<Option<T>>` for `First<T>` and `Last<T>`.
- Added `fold_with` monoid utility converting iterator items via `From<T>` (falling back to `Monoid::empty()`).
- Added `FunctionCategory` implementing `Category` and `Arrow` for Rust functions.

### Changed

- Separated `Category` morphism composition from `HKT` type constructors.
- Increased default stack size for `Validated` from 4 to 8 elements to reduce heap allocations.
- Simplified `PersistentVector`: removed `with_cache_policy`, `from_slice_with_cache_policy`, `with_chunk_size`, `ChunkIter`, and the `pvec` feature; chunk size is fixed at 64.
- Updated MSRV to 1.88.0.

### Removed

- **[Breaking]**: Removed `Foldable` implementations from monoid wrappers, `Composable`, `Value`, and `PersistentVector::to_arc()`; use `Arc::new(vector)` directly.

## [0.9.0]

### Added

- Added `modify` and `set_if_different` to `Prism` for structural sharing optimization (requires `S: Clone` and `A: PartialEq`).

### Breaking Changes

- Redesigned `Applicative` trait to align with category theory:
  - `apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>` where `Self::Source: Fn(&T) -> B` (function is in applicative context `F(A -> B)`).
  - `lift2<B, C, F>(&self, f: F, fb: &Self::Output<B>) -> Self::Output<C>` (function parameter comes first).
  - `lift3<B, C, D, F>(&self, f: F, fb: &Self::Output<B>, fc: &Self::Output<C>) -> Self::Output<D>` (function parameter comes first).

### Removed

- Removed `quickcheck` from `full` feature flag.

## [0.8.0]

### Changed

- Upgraded to Rust 2024 edition (MSRV 1.87.0).
- Clarified `Choice` filter semantics: `filter` applies only to alternatives (preserving primary), while `filter_value` applies to all values including primary.

### Removed

- Removed `IdentityExt` trait from `traits/identity.rs`.

### Fixed

- Fixed `Choice::flatten()` ordering: alternatives consist of remaining items from primary iterator followed by items from alternatives' iterators.
- Refined `IsoLens`: changed `set` signature to `set(&self, a: &A) -> S` (removing redundant `_s`), moved `Clone` bounds to impl block, corrected `modify` closure to `FnOnce(A) -> A`, and added `set_focus` and `modify_focus` helpers.
- Enhanced `Validated`: added safe `into_value()` and `into_error_payload()` accessors, panicking `unwrap_invalid_owned()`, zero-copy `fmap_invalid_owned()`, and non-cloning `value()` and `error_payload()`; removed `std_error` feature and source helpers.
- Modularized `Validated` test suite (`tests/datatypes/test_validated.rs`) into distinct trait law, panic, scenario, and property test modules.
- Encapsulated `Sum` wrapper internals: removed direct `new` and `inner` access in favor of monoid trait operations.

## [0.7.1]

### Added

- **Thread-safe Memoizer**: Introduced `Memoizer<K, V>` in `wrapper/memoizer.rs` using `RwLock<HashMap<K, V>>` (`get_or_compute`, `clear`), deprecating `ThreadSafeMemoizeFn`.
- **PersistentVector Path Caching**: Implemented path/range caching in RRB tree via `Node::get_with_path` and `get_by_path`; `get_with_cache` reuses traversal paths and invalidates cache on tree modifications.

### Changed

- **Writer Monad Refactoring**: Replaced recursive `LogThunk` with direct log accumulation in `Writer`, eliminating stack overflow risks and using immediate `Monoid` combination.

### Fixed

- Added `validate_cache_path` to `PersistentVector` tree to verify cached path and ranges against tree structure, safely treating stale entries as cache misses.

## [0.7.0]

### Added

- Added `iso_lens.rs` and `iso_prism.rs` for Iso-based optics (`Lens`/`Prism`) with lawful composition.
- Implemented `MonadPlus` and `Alternative` for `Maybe<T>`, `Either<L, R>`, `Validated<E, A>`, and `Choice<T>`.
- Added `Choice<T>::flatten_sorted()` to flatten and sort alternatives.
- Implemented `IntoIterator` for `Maybe`, `Validated`, `Id`, `Writer`, and `Either`.
- Enhanced `NaturalTransformation` trait with documentation, `transform_owned`, and `identity_nat`.

### Breaking Changes

- **Unified Transformer-to-Base Conversions via `From`**:
  - Removed `to_state`, `to_state_t`, `from_state_t`, `to_reader`, `from_reader`, `to_cont`, `from_cont` from `State`, `Reader`, and `Cont`.
  - Standardized conversions via `From`/`Into`:
    - `From<ReaderT<E, Id<A>, A>> for Reader<E, A>`
    - `From<StateT<S, Id<(A, S)>, A>> for State<S, A>`
    - `From<ContT<R, Id<R>, A>> for Cont<R, A>`
  - Migration example:

    ```rust
    let base: State<i32, i32> = State::from(state_t);
    let cont: Cont<i32, i32> = cont_t.into();
    let reader: Reader<i32, i32> = reader_t.into();
    ```

- Changed `Choice<T>::flatten()` to preserve original order (use `flatten_sorted()` for sorting).
- Refactored `Validated` to unify invalid cases using iterator-based error accumulation.
- Removed `WriterT` transformer.
- Refactored `prelude` into submodules (`traits`, `traits_ext`, `datatypes`, `wrapper`, `transformer`, `utils`).

## [0.6.4] - 2025-04-18

### Changed

- Reimplemented `Cont` as a thin wrapper delegating core operations (`new`, `run`, `pure`, `bind`, `fmap`, `apply`, `call_cc`) to `ContT`; updated closure signatures for `Cont::new` to match transformer conventions.

## [0.6.3] - 2025-04-17

### Added

- Introduced `ContT<R, M, A>` (Continuation Monad Transformer) with core methods (`new`, `run`, `pure`, `bind`, `fmap`, `apply`, `call_cc`, `lift`) and `MonadTransformer` implementation.

## [0.6.2] - 2025-04-17

### Added

- Added `CachePolicy` (`AlwaysCache`, `NeverCache`, `EvenIndexCache`) and dynamic cache policy constructors (`with_cache_policy`, `from_slice_with_cache_policy`) for `PersistentVector`.
- Added `is_empty_monoid()`, `repeat`, `mconcat`, and `power` to `Monoid`; implemented `Comonad` for `Option`, `Result`, and `Maybe`.
- Added `ResultValidatedIso` and converted `Iso` static methods to instance methods.

### Changed

- Optimized `PersistentVector` memory and performance; added `Index<usize>` and `IntoIterator`.
- Standardized error handling around `AppError` from `error_utils.rs`, replacing panics with composable `Result`s.
- Refactored `IO<A>` around `Arc<dyn Fn()>`; `delay` uses `std::thread::sleep` and `delay_efficient` uses `spin_sleep`.
- Consolidated `cache`, `chunk`, and `memory` into `memory.rs`.

### Fixed

- Fixed `SmallVec` slice initialization with compatibility-preserving loop.

## [0.6.1]

### Added

- Added inline storage for `PersistentVector` with $\le 8$ elements, `pop_back`, `to_arc`, and Rayon-based `par_map`.

## [0.6.0]

### Added

- Added `pvec` and `wrapper::memoize` modules (`MemoizeFn`, `MemoizeReader`); added `Identity`/`Functor` for `First`, `Last`, `Max`, `Min`, `Product`, `Sum`, `Value`; added `Monoid` for `Min`/`Max`.
- Added `DOCTEST_GUIDELINE.md`, `PERFORMANCE.md`, and `TUTORIAL.md`.
- Added `MaybeError`, `WithError`/`MaybeExt`, `to_standard_result()`, `try_unwrap()`, and `to_result<E>()`.
- Added Cats-style Reader/ReaderT conversions: `to_reader_t`, `to_reader`, `from_reader`, and `pure`.

### Changed

- Removed `transformers` and `advanced` feature flags; refactored `Reader` over `ReaderT`; removed `Id::map`; removed `Arc` from `Lens`/`Prism`.
- Simplified `Maybe`: removed `map`/`map_or_else`, renamed `map_or` to `fmap_or`; renamed `Either::map_left`/`map_right` to `fmap_left`/`fmap_right`.
- Simplified `Choice` around ownership operations: removed duplicate/reference variants, made `swap_with_alternative`/`add_alternative` defaults, and removed `change_first`, `all_values`, `find_alternative`, and `from_iterator`.

### Removed

- Removed `BoxedFn` (`wrapper/boxed_fn.rs`) and `Choice` helpers (`replace_alternatives_with_first`, `with_ordered_alternatives`/`_owned`, `with_unique_alternatives`/`_owned`, `partition`, `group_by`, `match_choice`/`_owned`, `zip`).

## [0.5.4] - 2025-03-24

### Added

- Implemented `StateT` with `get`/`put`/`modify`, `bind_with`/`fmap_with`, type aliases (`StateValueMapper`, `StateCombiner`), tests, and documentation.
- Added `Alternative`, `Distributive`, `Divisible`, `Iso`, `NaturalTransform`, and `Representable` traits.

### Changed

- Optimized `Choice` with `Arc`-based shared structure to reduce cloning.

## [0.5.3] - 2025-03-16

### Changed

- **`Choice` Enhancements**:
  - Changed `first()` to return `Option<&T>` instead of `&T` to safely handle empty choices.
  - Added `add_alternatives_owned`, `filter`, `change_first`, `swap_with_alternative`, `swap_with_alternative_owned`, `replace_alternatives_with_first`, and `replace_alternatives_with_first_owned`.

## [0.5.2] - 2025-03-09

### Changed

- Configured docs.rs with `all-features = true`.

## [0.5.1] - 2025-03-09

### Added

- Implemented `From`/`Into`, `Semigroup`, `Monoid`, `Foldable`, and `Composable` for `Id`.
- Added docs.rs configuration to display documentation for all features (`full`).

## [0.5.0] - 2025-03-09

### Added

- Added wrapper types: `boxed_fn`, `first`, `last`, `product`, `sum`, `value`, `thunk`, `min`, `max`.
- Added utilities: `hkt_utils`, `transform_utils`.
- Implemented functional traits for standard types (`Option`, `Result`, `Vec`).
- Added ownership-based trait methods (`fmap_owned`, `bind_owned`, `join_owned`, etc.).
- Added feature flags: `async`, `advanced`, `transformers`, and `full`.

## [0.4.0] - 2025-02-26

### Added

- Implemented `StateT` with `get`/`put`/`modify`, `bind_with`/`fmap_with`, type aliases (`StateValueMapper`, `StateCombiner`), tests, and documentation.
- Added `Alternative`, `Distributive`, `Divisible`, `Iso`, `NaturalTransform`, and `Representable` traits.

### Changed

- Optimized `Choice` with `Arc`-based shared structure to reduce cloning.

## [0.3.2] - 2025-02-18

### Added

- Added `Choice` data type for alternative computations.
- Added property-based tests for Applicative and Bifunctor laws.

### Changed

- Reorganized project structure: renamed `monads/` to `datatypes/` and `category/` to `traits/`.

## [0.3.1] - 2025-02-13

### Changed

- Modified `lift2` and `lift3` to accept tuples for function types.
- Updated category morphism definitions.
- Marked `Free` monad as work in progress.
- Refactored `FnType` methods into `FnTrait`.

### Removed

- Removed unnecessary function types.

## [0.3.0] - 2025-02-10

### Added

- Implemented Free Monad.
- Integrated `SendSyncFn`, `SendSyncFnTrait`, `ContravariantFn`, `ExtendFn`, `MonadFn`, and `ApplyFn` with `FnType` and `FnTrait`.
- Implemented `Arrow` and `Category`.
