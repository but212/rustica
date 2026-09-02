# CHANGELOG

## [Unreleased]

### Documentation Correctness

- Documented `Min<T>` and `Max<T>` as `Semigroup` wrappers without a generic `Monoid` identity. Use `semigroup::combine_all_values` for empty-capable reductions or provide a domain-specific extremum.

### Bug Fixes

- Fixed `PersistentVector::concat` ordering across unequal-height RRB trees.
- Fixed `PersistentVector::pop_back` to drain the front head buffer after the tree is exhausted.

### Tests

- Added regressions for unequal-height `PersistentVector::concat`, full head/tree `pop_back` draining, and `FoldableExt::fold_option` short-circuiting.
- Added compile-fail contracts for removed unlawful implementations and phantom marker wrappers.

### Changed

- Generalized `pipeline_result` from `Vec<Func>` to any `IntoIterator<Item = Func>`, matching `pipeline_option`; `Vec` still works.

### CI/CD and Security

- Added least-privilege workflow permissions, pinned external actions, and `actionlint`/`zizmor` checks.
- Declared the MSRV through Cargo's `package.rust-version` metadata and added a dedicated check.
- Hardened releases with locked packaging, exact CHANGELOG validation, a protected crates.io environment, and verified SLSA verifier downloads.
- Added trusted benchmark regression reporting with a 20% slowdown threshold; pull-request benchmark jobs remain read-only.
- Added repository ownership, security reporting, pull-request, and issue templates under `.github/`.

### Breaking Changes

- **Lawful Algebraic Trait Surface**
  - Removed `Monoid` for `Min<T>`/`Max<T>`; use `Semigroup::combine` with an explicit extremum or `combine_all_values` for empty-capable reductions.
  - Removed `MonadPlus` for `Result<T, E>` because arbitrary `E` has no lawful zero; use `Result::or_else`.
  - Removed unused `HKTType`/`PureType` phantom wrappers; use `HKT`, `Pure`, or `PureExt`.

- **Transformer State and Type Invariants**
  - `ReaderT<E, M, A>` requires `M: HKT<Source = A>`; type-changing operations return `M::Output<B>`, and the unsafe bind conversion was removed.
  - `StateT<S, M, A>` has one executable representation, requires `M: HKT<Source = (S, A)>`, and threads state left-to-right.
  - `StateT` no longer exposes `Pure` or `LiftM`; `MonadTransformer::BaseMonad` is the base family containing `A`, not `(S, A)`.

- **Error and Conversion API**
  - Removed impossible `ChoiceError::EmptyChoice`, `PVecError::InvalidRange`, and `IOError::ValueNotSet` variants.
  - Removed `ErrorOps`, `sequence`, `traverse`, and redundant free error-conversion functions; use `Result`/`Iterator` methods and `From`.
  - `Validated` converts from owned or borrowed `Result` through `From`; lossy conversion is `into_result_first_error`.
  - Replaced panicking `NonEmptyErrors` `FromIterator` with `NonEmptyErrors::try_from_iter`, returning `Option` for empty-capable input.
  - Removed panicking `Choice` conversions from `Vec`, slices, and iterators. Use `Choice::of_many` for `Option` or `TryFrom` for `Result<Choice<T>, ChoiceError>`; empty input returns `ChoiceError::EmptyInput`.

- **Dead Utilities Removed**
  - Removed empty `utils::categorical_utils`, the `utils::functions::id` alias, and unused `ReaderCombineFn`/`ContFn` aliases.

- **Duplicate Functional Data Types Removed**
  - Removed `Maybe<T>` in favor of standard `Option<T>` (which retains `Functor`, `Applicative`, `Monad`, and `Foldable` implementations).
  - Removed `Either<L, R>`, `EitherError`, `ResultEitherIso`, and `Either` conversion helpers in favor of `Result<R, L>` or the external `either` crate.

- **Single-Implementation Traits Removed**
  - Removed `Category`/`Arrow`; `FunctionCategory` now exposes morphism operations as inherent associated functions: `identity_morphism`, `compose_morphisms`, `arrow`, `first`, `second`, `split`, and `combine_morphisms`. `function!`, `compose!`, and `pipe!` no longer require trait imports.
  - Removed `Comonad`; `Id<T>` now provides `extract`, `duplicate`, and `extend` inherently.
  - Removed `Evaluate`/`EvaluateExt`; `Thunk` and `IO` expose `Thunk::evaluate` and `IO::run` inherently.

- **Redundant Wrappers & Pipelines Removed**
  - Removed `ErrorPipeline`/`error_pipeline` in favor of standard `Result` combinators, `ErrorCategory` in favor of `Result`/`Validated`, `Pipeline<T>` from `rustica::utils::transform_utils`, and `Memoizer` in favor of dedicated caching crates (`lru`, `moka`).

- **Collection Iterator Helpers Removed**
  - Removed `PersistentVector::take`/`skip`; use iterator adapters or `PersistentVector::split_at`.

### Maintenance

- Added central compile-fail removal contract doctests in `src/lib.rs`.
- Updated all doc examples and benchmarks to the 0.14.0 API.
- Persistent vectors derive length from their representation and compare/hash by logical element sequence; removed the unused generation counter.
- Added a targeted Miri CI test for owning `ReaderT::bind` values, removed redundant phantom fields, and removed the unused futures `thread-pool` feature.

## [0.13.0]

### Maintenance - 0.13.0

- Relaxed owned error-conversion helpers to accept non-`Clone` values and simplified `Result` sequencing/pipelines with iterator combinators.
- Kept `ErrorPipeline` behavior unchanged; migrate to native `Result` combinators before its planned 0.14.0 removal.

### Breaking Changes - 0.13.0

- **`Choice<T>` Impossible-State Elimination**
  - Redesigned `Choice<T>` as `{ primary: T, alternatives: SmallVec<[T; 7]> }`, making empty choices impossible at compile time. `first()` returns `&T`; removed `new_empty()`; added `single()`, `of_many()` (`Option<Choice<T>>`), and `filter_values()`.
  - Implemented `Pure`, `Functor`, `Applicative`, `Monad`, `Semigroup`, `IntoIterator`, and `Foldable` for `Choice<T>`.

- **`NonEmptyErrors<E>` Invariant Preservation**
  - Removed `NonEmptyErrors::remove()` so error collections cannot become empty.

- **Dead Code and Speculative Helpers Removed**
  - Removed the 0-impl `Traversable` trait and dead utilities `const_fn`, `compose`, `pipe`, `flip`, `fold_with`, `bimap_result`, `fan_out`, `compose_all`, `lift_option`, and `transform_all`.
  - Re-exported `id` directly from `std::convert::identity`.

- **Deprecations (0.14.0 Complete Removal Notice)**
  - Deprecated `Maybe<T>` (use `Option<T>`), `Either<L, R>` (use `Result<R, L>` or `either`), one-implementation traits (`Comonad`, `Arrow`, `Category`, `Evaluate`, `EvaluateExt`), speculative wrappers (`ErrorCategory`, `ErrorPipeline`, `Pipeline<T>`, `Memoizer`), and `PersistentVector::{take, skip}`.

- **`Validated<E, A>` Non-Empty Error Invariant**
  - `Invalid` now stores `NonEmptyErrors<E>`; `invalid_many` rejects empty input, while `try_invalid_many` supports it. Serde rejects empty invalid arrays without changing the JSON representation. Removed `invalid_vec` and `error_buffer_mut`.

- **Legacy and Redundant APIs Removed**
  - Removed legacy `Choice` mutation/iteration helpers, `PersistentVector` cache-policy constructors, `ResultExt`, `try_pipeline`, `compose_when`, stdlib-equivalent categorical collection helpers, `SemigroupExtAdapter`, and `combine_all_owned`. Use documented conversion functions and standard `Option`/`Result`/`Iterator` APIs.

- **Semigroup Repetition Contract**
  - `SemigroupExt::combine_n` and `combine_n_owned` now require `NonZeroUsize`, eliminating zero-count states.

### Changed - 0.13.0

- Removed confirmed redundant clones across all targets; strict `clippy::redundant_clone` passes. `FoldableExt::to_vec` now appends into one accumulator (O(n), formerly O(n²)).
- `PersistentVector` builds owned trees leaf-by-leaf, shares one recursive builder, and moves uniquely owned leaves during consuming conversion. Vec/Choice applicatives write directly to final collections; error display and owned panic payloads avoid clones.
- `ReaderT`/`StateT` callback adapters borrow `dyn Fn` callbacks; `ReaderT::lift2` returns an opaque callable. Memoizer insertion uses move replacement, named `InsertOutcome`, and limits `V: Clone` to owned-copy APIs; zero-capacity caches stay disabled.
- Validated paths share an `ErrorAccumulator` while preserving error order/accumulation; `traverse_validated` no longer requires `E: Clone`.
- Single-value `Either`/`Validated` iterators use `Option::IntoIter`; Tokio uses `std::sync::LazyLock`; `rayon`/`lazy_static` are not normal runtime dependencies, `quickcheck` is optional, and `serde_json` is dev-only.

### Fixed - 0.13.0

- Fixed owned semigroup repetition that could duplicate the accumulated value and owned `Validated` conversion that mishandled singleton errors.

See [MIGRATION_v0.13.0.md](MIGRATION_v0.13.0.md) for migration details.

## [0.12.0]

### Breaking Changes - 0.12.0

- **`Choice<T>` Typeclass Cleanup**
  - Removed deprecated methods and functions

## [0.11.1]

### Added - 0.11.1

- **`Lens<S, A>` Composition Methods**
  - Added `compose()` and fluent `then()` for type-safe nested lens access; e.g. `address_lens.compose(street_lens)` creates a lens from Person to street.
- **`Prism<S, A>` Composition Methods**
  - Added `compose()` and fluent `then()` for type-safe nested sum-type access; e.g. `outer_prism.compose(inner_prism)` creates a prism from Outer to inner value.

### Performance Optimizations

- **`Validated<E, A>` SmallVec Capacity Reduced**
  - Changed inline error storage from `SmallVec<[E; 8]>` to `[E; 4]`, preserving common-case performance while halving stack usage.

### Fixed - 0.11.1

- **Memoizer::with_capacity(0) Behavior**
  - Zero capacity now creates a disabled cache instead of an unbounded one.

## [0.11.0]

### Breaking Changes - 0.11.0

- **`utils::hkt_utils::map_result` Consolidated**
  - Consolidated into `categorical_utils`; `hkt_utils::map_result` remains a backward-compatible re-export. Prefer `categorical_utils::map_result`, which accepts `FnOnce` instead of `Fn`.
- **`Validated<E, A>` Typeclass Cleanup**
  - Removed `Monoid` (no lawful identity for accumulation), `AsRef<A>` (it panicked on `Invalid`), `MonadPlus`, and `Alternative`; use `Validated::valid(...)`, `Validated::as_ref()`/pattern matching, or `recover_all`, `recover_all_at_once`, and `sequence_owned` as appropriate.
- **`Either<L, R>` Typeclass Cleanup**
  - Removed `MonadPlus`; use `Alternative` for choice semantics.
- **`Choice<T>` Typeclass Cleanup**
  - Removed duplicate `MonadPlus`; migrate `mzero()` → `Alternative::empty_alt()` and `mplus()` → `alt()`. `Foldable` no longer requires `T: Clone`.
- **`utils::error_utils` Module Removed**
  - Moved `WithError`, `ResultExt`, `sequence`, `traverse`, and related utilities to `crate::error`; migrate `rustica::utils::error_utils::*` to `rustica::error::*` or `rustica::prelude::error::*`.
- **Identity Trait and Implementations**
  - Removed deprecated `Identity` and `traits::identity`, including implementations for `Id`, `Maybe`, `Either`, `Validated`, `Choice`, `PersistentVector`, `First`, `Last`, `Max`, `Min`, `Product`, `Sum`, and `Writer`.
- **Legacy `AppError` Utilities**
  - Removed `AppError`, `error()`, and `error_with_context()`; route public error construction through `crate::error::ComposableError` and its context helpers.

### Changed - 0.11.0

- **Core Error Helper Cleanup**
  - `Either::to_result` / `from_result` now delegate to `crate::error::{either_to_result, result_to_either}`
  - `IO::try_get`, `IO::try_get_with_context`, and `Maybe::try_unwrap` now return `ComposableResult` for consistency

- **Error Prelude Consolidation**
  - `prelude::error` re-exports unified error module: `ComposableError`, `ComposableResult`, boxed variants, context utilities, `WithError`, `ResultExt`

- **`Choice<T>` Documentation Clarification**
  - `Semigroup::combine` and `Alternative::alt` share the same "merge alternatives" behavior for `Choice<T>`
  - `flatten()` panics when the primary iterator is empty; use `try_flatten()` for a safe alternative

- **`Choice<T>` Safe Methods Signature Changes**
  - `try_remove_alternative()`, `try_flatten()`, and `try_swap_with_alternative()` now return `ChoiceError`-based `Result`s instead of `&'static str`; added non-panicking `try_first()`. Migrate to `ChoiceError` variants.
- **`Either<L, R>` Safe Methods Added**
  - Added `try_unwrap_left()`, `try_unwrap_right()`, `try_left_ref()`, and `try_right_ref()`, returning `Result<_, EitherError>` instead of panicking.
- **`Validated<E, A>` Safe Methods Added**
  - Added `try_unwrap()`, `try_unwrap_invalid()`, and `try_valid_ref()`, returning `Result<_, ValidatedError>` instead of panicking.
- **New Error Types in `datatypes::error`**
  - Added structured `ChoiceError` (`NoAlternatives`, `IndexOutOfBounds`, `EmptyPrimaryIterator`, `EmptyChoice`), `EitherError` (`ExpectedLeft`, `ExpectedRight`), and `ValidatedError` (`ExpectedValid`, `ExpectedInvalid`).
- **Unused Trait Modules Removed**
  - Removed unused placeholder modules `contravariant_functor`, `natural_transformation`, `profunctor`, and `representable`.

- **`Validated<E, A>` Performance and API Improvements**
  - `iter_errors()` now matches `iter_errors_mut()` with `ErrorsIter`; `collect()`/`collect_owned()` require only `C: FromIterator<A>`; direct `extend()` removes iterator overhead.
  - Added zero-copy `as_option()`/`into_option()` while retaining `to_option()` (`A: Clone`), and async owned `fmap_valid_async_owned()`, `fmap_invalid_async_owned()`, and `and_then_async_owned()` using `FnOnce` to avoid clones.
- **`PersistentVector<T>` Performance and API Improvements**
  - Stack-based traversal reduces full iteration from O(n log n) to O(n); `fold_right` uses `DoubleEndedIterator`; and `get()`, indexing, borrowed iteration, and `Foldable` no longer require `T: Clone`.
  - Added independent front/back cursors for efficient bidirectional `.rev()` chains.

- **`Memoizer` Improvements**
  - Added bounded O(1) LRU eviction via `with_capacity(max)`, statistics (`stats`, `hit_rate`, `reset_stats`, `max_capacity`), manual/fallible operations (`insert`/`try_insert`, `get_or_try_compute`, `touch`/`try_touch`), and `MemoizerError`-returning `try_*` methods for lock poisoning.
  - Added `len`/`try_len`, `is_empty`/`try_is_empty`, `contains_key`/`try_contains_key`, `remove`/`try_remove`, `get`/`try_get`, `reserve`/`try_reserve`, `shrink_to_fit`/`try_shrink_to_fit`, `keys`/`try_keys`, `values`/`try_values`, `capacity`/`try_capacity`, and `clear`/`try_clear`.
  - Fixed optimistic computation to return a concurrently cached value, disabled capacity-zero caches, and clarified `get()` versus `peek()` LRU semantics.

## [0.10.2]

### Deprecated - 0.10.2

- **`Choice<T>` Utility Methods**
  - Deprecated until v0.12.0: `has_alternatives()` (use `!alternatives().is_empty()`), `to_vec()` (use `Into::<Vec<T>>::into()` or `.iter().cloned().collect()`), `find_first()` (use `iter().find()`), `dedup()`/`dedup_by_key()` (use external iteration), `fold()` (use `Foldable::fold_left`/`fold_right`), `to_map_with_key()` (use `iter().map().collect()`), `add_alternatives()` (use `Semigroup::combine()` or Monoid operations), `remove_alternative()`/`try_remove_alternative()` (use `filter_values()`), `filter()` (use `filter_values()`), `fmap_alternatives()` (use `fmap()` or external iteration), `flatten_sorted()` (use `flatten()` then sort), `iter_alternatives()` (use `alternatives().iter()`), `swap_with_alternative()`/`try_swap_with_alternative()` (use external patterns), and `bind_lazy()` (use `bind()` with `into_iter()` or `flat_map`).
- **Legacy Error Utilities (`utils::error_utils`)**
  - Deprecated in favor of `crate::error`: `result_to_either()` → `crate::error::result_to_either()`, `either_to_result()` → `crate::error::either_to_result()`, `ResultExt::to_validated()` → `crate::error::result_to_validated()`, `ResultExt::to_either()` → `crate::error::result_to_either()`, and `ResultExt::bimap()` → `crate::error::ErrorOps::bimap_result()`.
  - Deprecated `AppError<M, C>` and `error()`/`error_with_context()` in favor of `ComposableError` and `ComposableError::new(...).with_context(...)`.

### Breaking Changes - 0.10.2

- **Composable Error Helpers Replace `AppError` in Core Datatypes/Transformers**
  - `State`, `Maybe`, `IO`, `ReaderT`, and `StateT` `try_*` helpers now return `ComposableResult`/`ComposableError`. Legacy types, constructors, and examples were removed; migrate to `core_error()` and `context()` (context stacks compare as `Vec<String>`).
- **`src/error` Module API Changes**
  - Removed redundant `with_context_result_boxed()`; use `with_context_result()`.
  - `ErrorPipeline::finish()` now returns `Result<T, Box<ComposableError<E>>>` instead of `Result<T, ComposableError<E>>`, enabling deep buffering without large `Result` values or stack-overflow risk.
- **`Validated` Error Handling API Changes**
  - Removed its `ErrorOps` implementation because `ErrorOps::recover` conflicts with accumulation; use `recover_all` or `recover_all_at_once` in `src/datatypes/validated/core.rs`.

### Changed - 0.10.2

- **`Choice<T>` Refocused on Core Categorical Operations**
  - Retained the essential Functor/Applicative/Monad/MonadPlus API: `new`, `new_empty`, `first`, `alternatives`, `len`, `is_empty`, `filter_values`, `flatten`, `try_flatten`, `of_many`, `iter`, and trait implementations; deprecated utility methods to reduce the surface.
- **`Choice<T>` Memory Management Optimization**
  - Replaced `Arc<SmallVec<[T; 8]>>` with directly owned `SmallVec<[T; 8]>`, eliminating reference-counting/copy-on-write overhead and broken `Arc::try_unwrap` paths. This improves `filter`/`map`/`bind`, reduces small-choice memory by ~40%, and preserves stack storage/cache locality for ≤8 items.
- **`AsyncM` Performance Optimization**
  - Added Cats Effect/ZIO-inspired Pure and Pure+Pure fast paths (including `apply`/`zip_with`), aggressive inlining, and an `AsyncMInner` Pure/Lazy enum. Specialized `fmap`, `bind`, `apply`, and `zip_with` paths reduce `Arc` cloning and lazy-only matching.
- **`IO` Changes**
  - **Breaking Change**: `apply` now follows the Applicative pattern `IO<A>.apply(IO<Fn(A) -> B>) -> IO<B>`; the former `IO<A>.apply(Fn(A) -> IO<B>)` alias for `bind` was removed.
  - Added AsyncM-inspired Pure+Pure and mixed Pure/Effect fast paths, aggressive inlining, optimized `new`/`run`/`pure`/`fmap`/`bind`/`apply`/`is_pure`/`is_effect`, and Pure-vs-Effect benchmarks.
- **`src/error` Module Performance Optimization**
  - Removed `with_context()` closure overhead via inline matching and buffered contexts in `SmallVec<[String; 4]>` rather than transforming each `Result<T, E>` immediately. `map`, `and_then`, `recover`, and `map_error` preserve buffers; `finish()` returns `Result<T, Box<ComposableError<E>>>`.
  - Standardized context functions on `Into<String>`; `ComposableError` keeps O(1) `push()` storage and backward-compatible most-recent-first ordering while preserving categorical correctness.
- **`Validated` Error Accumulation Optimizations**
  - Added reusable `ErrorAccumulator` storage backed by `SmallVec<[E; 8]>`, owned `combine_errors_owned`/`sequence_owned`/`collect_owned` variants, zero-copy `error_slice`/`error_buffer_mut` accessors, and iterator improvements without `Clone` bounds. Documented the borrowed/owned split and added regression tests.

## [0.10.1]

### Breaking Changes - 0.10.1

- **Identity Trait Deprecation**
  - Deprecated `Identity` because of design flaws; `Functor` now extends `HKT` directly, and `id()` moved to `utils::functions`. Added `MIGRATION_v0.11.0.md`.

### Added - 0.10.1

- **Function Utilities**
  - Added `utils::functions::{id, const_fn}`.
- **Documentation**
  - Documented `PersistentVector`, added `pipe` to `utils::transform_utils`, and added the migration guide.
- **Enhanced IO Monad Error Handling**
  - Integrated `src/error` with `try_get_composable()`, `try_get_composable_with_context()`, `into_error_pipeline()`, `recover()`, `recover_with()`, and `sequence_composable()`.
  - Added `ComposableError` context stacking and preserved full error chains/context through IO; `ErrorPipeline` provides type-safe transformations after `Result` extraction while retaining `try_get()` compatibility.

### Changed - 0.10.1

- **IO Error Semantics**
  - Updated ComposableError documentation, recovery guidance, and Quick Start examples.

### Fixed - 0.10.1

- **Category Theory Compliance**
  - `Functor` now extends only `HKT`, separating value extraction from functor operations.
- **compose function order**
  - Fixed compose order in tests.
- **Error Handling Doctests**
  - Fixed `map_error` doctests by removing problematic methods and improving examples.

### Deprecated - 0.10.1

- **Identity Trait**
  - Deprecated until v0.12.0; use `unwrap()`, `as_ref()`, or `Comonad::extract()`.

## [0.10.0]

### Added - 0.10.0

- **Wrapper From/Into trait implementation**
  - Added direct `From<T>`/`Into<T>` support for `Sum<T>`, `Product<T>`, `Min<T>`, `Max<T>`, and `Value<T>`, plus `From<Option<T>>` for `First<T>` and `Last<T>`.
- **Monoid utility function**
  - Added `fold_with`, which converts iterator items via `From<T>`, uses the first item when present, and `Monoid::empty()` for empty input.
- **Function Category implementation**
  - Added `FunctionCategory` implementing `Category` and `Arrow` for Rust functions.

### Changed - 0.10.0

- **Category trait inheritance removed from HKT**
  - `Category` now handles morphism composition independently; `HKT` remains focused on type constructors.
- **Increased default stack size for `Validated` from 4 to 8 elements** to reduce heap allocation.
- **Change and simplify `PersistentVector`**
  - Removed `with_cache_policy`, `from_slice_with_cache_policy`, `with_chunk_size`, `ChunkIter`, and the `pvec` feature; chunk size is fixed at 64.
- **MSRV updated to 1.88.0**

### Removed - 0.10.0

- [BREAKING CHANGE] Removed `Foldable` implementations from monoid wrappers, `Composable`, `Value`, and `PersistentVector::to_arc()`; use `Arc::new(vector)` for standard Arc wrapping.

## [0.9.0]

### Added - 0.9.0

- **Prism structural sharing optimization methods**
  - Added `modify` method to `Prism` for structural sharing optimization: returns the original structure if the value is unchanged after transformation, avoiding unnecessary allocations and copies.
  - Added `set_if_different` method to `Prism`: only creates a new structure if the new value differs from the current value.
  - Both methods require `S: Clone` and `A: PartialEq` constraints for efficient comparison and sharing.
  - Enhanced documentation with practical usage examples.

### Change - 0.9.0

#### BREAKING CHANGES - 0.9.0

- **Complete redesign of `Applicative` trait** to align with mathematical definition from category theory
- **Method signature changes**:
  - `apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>` where `Self::Source: Fn(&T) -> B`
    - Function is now IN the applicative context (F(A->B)), value is the parameter
  - `lift2<B, C, F>(&self, f: F, fb: &Self::Output<B>) -> Self::Output<C>`
    - Function parameter now comes FIRST (matches Haskell/Cats convention)
  - `lift3<B, C, D, F>(&self, f: F, fb: &Self::Output<B>, fc: &Self::Output<C>) -> Self::Output<D>`
    - Function parameter now comes FIRST

### Removed - 0.9.0

- remove quickcheck in full feature flag

## [0.8.0]

### Changed - 0.8.0

- Upgraded to Rust 2024 edition with minimum supported version 1.87.0

- **`Choice` Filter Methods Clarification** (`src/datatypes/choice.rs`)
  - Established clear division of responsibilities between filter methods:
    - `filter`: Only applies the predicate to alternative values, always preserves the primary value
    - `filter_value`: Applies the predicate to all values including primary
  - Updated documentation and tests to reflect this design decision

### Removed - 0.8.0

- removed `IdentityExt` trait from `traits/identity.rs`

### Fixed - 0.8.0

- **`Choice::flatten()` Ordering Logic** (`src/datatypes/choice.rs`)

  - Corrected the implementation of `flatten` to match its documentation. The new alternatives now correctly consist of the remaining items from the primary iterator, followed by the items from the alternatives' iterators.

- **`IsoLens` API and Constraint Refinements** (`src/datatypes/iso_lens.rs`)

  - **API Consistency:** The `set` method signature was changed from `set(&self, _s: &S, a: &A) -> S` to `set(&self, a: &A) -> S`, removing the redundant `_s` parameter as the `Iso`'s `backward` method inherently reconstructs `S` from `A`.
  - **Type Constraints:** The `S: Clone` and `A: Clone` type constraints were moved to the main `impl<S, A, L> IsoLens<S, A, L>` block, enhancing generality and removing redundancy from individual methods.
  - **`modify` Method:** The `modify` method was updated to use the new `set` signature and its closure signature was corrected to `F: FnOnce(A) -> A` for accurate ownership transfer.
  - Documentation examples were updated to reflect these API changes.
  - **Documentation Clarity:** Added a "Semantic Note" to `IsoLens` documentation, explaining how the `Iso`'s target type `A` (typically `(FocusType, S_Context)`) enables traditional lens behavior by allowing reconstruction of `S` while preserving non-focused parts.
  - **Ergonomic Helper (`set_focus`):** Introduced `set_focus(&self, s: &S, new_focus_value: &FocusType) -> S` method for `IsoLens<S, (FocusType, S), L>`. This provides a more direct way to update the focused part, reducing boilerplate for common use cases.
  - **Ergonomic Helper (`modify_focus`):** Added `modify_focus<F>(&self, s: &S, f: F) -> S` method for `IsoLens<S, (FocusType, S), L>`, where `F: FnOnce(FocusType) -> FocusType`. This complements `set_focus` by allowing direct, efficient transformation of the focused part.

- **`Validated` Datatype Refinement & Enhancement**
  - **Documentation Overhaul:**
    - Added a comprehensive, real-world "User Registration" example to demonstrate applicative validation for forms.
    - Included detailed explanations for type parameter constraints (e.g., why `E: Clone` is often needed) and the behavior of trait implementations like `Alternative::empty`.
  - **API Safety and Ergonomics:**
    - Introduced `into_value()` and `into_error_payload()` as safe, non-panicking methods to consume a `Validated` instance and extract its contents.
    - Added `unwrap_invalid_owned()` for ownership-based, panicking extraction of errors.
    - Clarified the distinction between `invalid_vec` (panics on empty input) and `invalid_many` (handles empty input gracefully) with improved documentation and examples.
  - **Performance Optimization:**
    - Added `fmap_invalid_owned`, an ownership-taking variant of `fmap_invalid`, to avoid unnecessary cloning of the `Valid` value.
    - Added `value()` and `error_payload()` methods to provide non-cloning, read-only access to the contained data.
- **`Validated` Test Suite Refactoring & API Cleanup**

  - The test suite for `Validated` (`tests/datatypes/test_validated.rs`) has been completely refactored into a modular structure for improved clarity, maintainability, and coverage.
  - Trait law tests, panic tests, scenario tests, and property-based tests are now organized into distinct modules.
  - Removed the `std_error` feature and its associated helper methods (`first_error_source`, `iter_error_sources`) to streamline the API.

- **`Sum` Wrapper Refinement** (`src/datatypes/wrapper/sum.rs`)
  - Internal implementation details of the `Sum` wrapper have been encapsulated.
  - Direct construction via `new` and direct access to the `inner` value are no longer part of the public API, promoting the use of trait-based operations (e.g., `Monoid::empty()`, `Semigroup::combine()`).
  - Enhanced performance-related documentation with more diverse examples and clearer explanations of its use as a monoidal accumulator.

## [0.7.1]

### Added - 0.7.1

- **Thread-safe Memoizer**
  - Introduced `Memoizer<K, V>` in `wrapper/memoizer.rs` as a new, ergonomic, and efficient thread-safe memoization utility.
  - Uses `RwLock<HashMap<K, V>>` for concurrent caching of pure function results.
  - Provides a unified API (`get_or_compute`, `clear`) for safe, concurrent memoization.
  - Includes comprehensive documentation and doctests for both single-threaded and multi-threaded use cases.
  - Deprecated the old `ThreadSafeMemoizeFn` in favor of this new implementation.
- **Path Caching for PersistentVector Tree**
  - Implemented path/range caching in the internal tree structure for `PersistentVector`.
  - Added `get_with_path` and `get_by_path` methods to `Node<T>` to record and utilize traversal paths and ranges for efficient repeated access.
  - The tree’s `get_with_cache` now records and reuses traversal paths, improving cache hit performance for repeated or nearby accesses.
  - Added validation logic `validate_cache_path` to ensure cached paths/ranges are only used when still valid for the current tree structure.
  - Tree modifications (push, update, split, etc.) automatically invalidate the cache to prevent stale accesses.

### Changed - 0.7.1

- **Writer Monad Refactoring**
  - Replaced the recursive LogThunk structure with direct log accumulation in the Writer struct.
  - Eliminated risk of stack overflow and memory leaks from deep thunk chains.
  - Simplified log combination logic to use immediate Monoid operations.

### Improvements & Bug Fixes - 0.7.1

- Added validation logic for path/ranges cache in PersistentVector tree.
  - Now, when the tree structure changes or if the cached path/ranges are no longer valid, the cache is safely treated as a miss.
  - Introduced the `validate_cache_path` method, which ensures that the cached path and ranges match the current tree structure before using the cache in `get_with_cache`.
  - Tree-modifying operations (such as push, update, etc.) continue to invalidate the cache to ensure consistency.

## [0.7.0]

### Added - 0.7.0

- Added `iso_lens.rs` and `iso_prism.rs` for Iso-based optics (Lens/Prism) with lawful composition, full documentation, and doctest examples.
- `IsoLens` and `IsoPrism` now support lawful composition for deep, type-safe focusing into nested product/sum types.
- **MonadPlus** and **Alternative** traits implemented for core datatypes:
  - `Maybe<T>`, `Either<L, R>`, `Validated<E, A>`, `Choice<T>`: All now support monadic choice, failure, and error accumulation where appropriate.
  - `Alternative` trait: Supported for `Maybe<T>`, `Either<L, R>` (with `L: Default`), `Validated<E, A>` (with `E: Default`).
- `Choice<T>::flatten_sorted()`: Flattens and sorts alternatives; see below for example.
- Iterator support (`IntoIterator`) for all core datatypes: `Maybe`, `Validated`, `Id`, `Writer`, `Either` (including left/right iterators). All implementations are documented and tested for idiomatic Rust usage.

  Example:

  ```rust
  let nested = Choice::new(vec![3, 1], vec![vec![5, 2], vec![4]]);
  let flat = nested.flatten_sorted();
  assert_eq!(*flat.first().unwrap(), 3);
  assert_eq!(flat.alternatives(), &[1, 2, 4, 5]);
  ```

### Changed - 0.7.0

- **[Breaking] Changed `Choice<T>::flatten()` behavior:**
  - Now preserves original order; sorting is provided by `flatten_sorted()`.
- **[Breaking] Refactored `Validated` datatype:**
  - Unified invalid cases, now uses iterators for error accumulation.
- **[Breaking] Removed `to_state`, `to_state_t`, `from_state_t`, `to_reader`, `from_reader`, `to_cont`, `from_cont` methods from State/Reader/Cont:**
  - All transformer-to-base conversions are now handled via the `From` trait (see below for migration).
- **[Breaking] Removed WriterT transformer:**
  - The WriterT transformer and all related code have been deleted.
  - WriterT is rarely useful in practical Rust code; most logging/accumulation use-cases are better served by explicit fields or iterators.
  - If monadic logging is needed, consider direct accumulation patterns or external loggers instead.
- **[Breaking] Refactored the `prelude` module:**
  - Prelude is now split into multiple logical modules: `traits`, `traits_ext`, `datatypes`, `wrapper`, `transformer`, and `utils` under `src/prelude/`.
  - Added `prelude::traits_ext` for extension traits (e.g., `EvaluateExt`, `FunctorExt`, etc.).
  - Users can now selectively import only the needed prelude components, improving ergonomics and compile times.
  - Top-level `prelude` now re-exports all submodules for convenience.
- **Enhanced `NaturalTransformation` trait:**
  - Added documentation, usage examples, and improved ergonomics.

## [Unifying Transformer Conversions]

### Breaking Change: Unified Transformer-to-Base Conversions via `From` Trait

- All conversions from transformer types to their respective base types are now standardized using the `From` trait:
  - `From<ReaderT<E, Id<A>, A>> for Reader<E, A>`
  - `From<StateT<S, Id<(A, S)>, A>> for State<S, A>`
  - `From<ContT<R, Id<R>, A>> for Cont<R, A>`
- Legacy conversion methods such as `to_reader`, `from_reader`, `to_state`, `from_state`, `to_cont`, `from_cont` have **all been removed** from the codebase.
- This change ensures a clear, unified, and idiomatic Rust API for all monad/transformer conversions.

#### Migration Guide

- To convert from a transformer to a base type, use the `From` trait or `.into()`:

  ```rust
  let base: State<i32, i32> = State::from(state_t);
  let cont: Cont<i32, i32> = cont_t.into();
  let reader: Reader<i32, i32> = reader_t.into();
  ```

- Update any code using the removed methods to use the `From` trait or `.into()` instead.

## [0.6.4] - 2025-04-18

### Changed - 0.6.4

- **Continuation Monad (`Cont`) Refactored**
  - `Cont` is now implemented as a thin wrapper over the more general `ContT` (Continuation Monad Transformer).
  - All core logic and methods (`new`, `run`, `pure`, `bind`, `fmap`, `apply`, `call_cc`, etc.) delegate to `ContT` for improved modularity and code reuse.
  - This refactor enables seamless integration with other monads and makes the continuation monad implementation more idiomatic and extensible.
  - The public API remains mostly unchanged, but closure signatures for `Cont::new` are now more ergonomic and consistent with transformer usage.
  - Comprehensive documentation and tests updated to reflect the new structure.

## [0.6.3] - 2025-04-17

### Added - 0.6.3

- **Continuation Monad Transformer (`ContT`)**
  - Introduced `ContT<R, M, A>`, a monad transformer version of the continuation monad.
  - Provides core methods: `new`, `run`, `pure`, `bind`, `fmap`, `apply`, `call_cc`, and `lift`.
  - Implements the `MonadTransformer` trait for seamless integration with other monads.
  - Comprehensive documentation and usage examples included.
  - Fixes and improvements for trait bounds and closure handling for safe, idiomatic Rust.

## [0.6.2] - 2025-04-17

### Added - 0.6.2

- **Flexible caching policy system for PersistentVector**
  - Added `CachePolicy` with `AlwaysCache`, `NeverCache`, `EvenIndexCache`, dynamic `with_cache_policy`/`from_slice_with_cache_policy` APIs, and custom-strategy documentation.

### Changed - 0.6.2

- **Persistent Vector Improvements**
  - Optimized performance/memory, refactored API/docs, added `Index<usize>`/`IntoIterator`, and expanded indexing, iteration, and edge-case tests.
- **Error Handling Standardization**
  - Unified errors around `AppError` from `error_utils.rs`, replaced most panics with composable `Result`s, and added contextual error documentation.
- **Monoid & Comonad Enhancements**
  - Added `is_empty_monoid()`, `repeat`, `mconcat`, and `power`; implemented `Comonad` for `Option`, `Result`, and `Maybe`.
- **Iso Trait Enhancements**
  - Added `ResultValidatedIso` and changed static methods to instance methods for composability.

### Fixed - 0.6.2

- SmallVec slice initialization now uses a compatibility-preserving loop.

### Refactored - 0.6.2

- Unified `cache`, `chunk`, and `memory` in `memory.rs`; removed dead code and improved formatting.

### IO Monad Improvements - 0.6.2

- Refactored `IO<A>` around `Arc<dyn Fn()>`; `pure`, `delay`, and `delay_efficient` minimize repeated-run cloning. `delay_efficient` uses `spin_sleep`, while `delay` uses `std::thread::sleep`.
- Documented blocking/spinning trade-offs, async/await extensions, error handling, and large-chain performance; improved doctests.

## [0.6.1]

### Added - 0.6.1

- Added inline storage for PersistentVector vectors ≤8 elements (up to 97% faster empty creation and ~5% faster pushes), plus `pop_back`, `to_arc`, expanded docs/doctests/README guidance, and async-feature `par_map` via Rayon.

## [0.6.0]

### Added - 0.6.0

- Added `pvec` and `wrapper::memoize` modules with `MemoizeFn`, `MemoizeReader`, collection support, wrapper memory optimization, and `Identity`/`Functor` implementations for `First`, `Last`, `Max`, `Min`, `Product`, `Sum`, and `Value`; added `Monoid` for `Min`/`Max`.
- Added `DOCTEST_GUIDELINE.md`, `PERFORMANCE.md`, and `TUTORIAL.md`.
- Added `MaybeError`, `WithError`/`MaybeExt`, `to_standard_result()`, `try_unwrap()` (`Result<T, AppError>` with context), `to_result<E>()`, and comprehensive Maybe error tests.
- Added Scala Cats-style Reader/ReaderT conversions: `to_reader_t`, `to_reader`, `from_reader`, and `pure`.

### Changed - 0.6.0

- Removed `transformers`/`advanced` feature flags; refactored `Reader` over `ReaderT`; removed `Id::map`; removed `Arc` from `Lens`/`Prism`.
- Simplified `Maybe`: removed `map`/`map_or_else`, renamed `map_or` to `fmap_or`; renamed `Either::map_left`/`map_right` to `fmap_left`/`fmap_right`.
- Simplified `Choice` around ownership-based operations: removed duplicate/reference variants, made `swap_with_alternative`/`add_alternative` the defaults, and removed `change_first`, `all_values`, `find_alternative`, and `from_iterator`.
- Standardized Maybe error handling, messages, context, and `Maybe`/`Option`/`Result` conversions.

### Removed - 0.6.0

- Removed `BoxedFn` (`wrapper/boxed_fn.rs`) and Choice helpers `replace_alternatives_with_first`, `with_ordered_alternatives`/`_owned`, `with_unique_alternatives`/`_owned`, `partition`, `group_by`, `match_choice`/`_owned`, and `zip`.

## [0.5.4] - 2025-03-24

### Added - 0.5.4

- Implemented `StateT` with `get`/`put`/`modify`, `bind_with`/`fmap_with`, type aliases (`StateValueMapper`, `StateCombiner`), tests, and usage documentation.
- Added `Alternative`, `Distributive`, `Divisible`, `Iso`, `NaturalTransform`, and `Representable` traits.

### Changed - 0.5.4

- Optimized `Choice` with `Arc`-based shared structure, reducing internal cloning and updating related methods, docs, and examples.

## [0.5.3] - 2025-03-16

### Changed - 0.5.3

- Enhanced `Choice` data structure:
  - Modified `first()` method to return `Option<&T>` instead of `&T` for better safety
  - Added support for handling empty `Choice` instances
  - Added `add_alternatives_owned` method to add multiple alternatives at once
  - Added `filter` method to filter alternatives based on a predicate
  - Added `change_first` method to replace the primary value
  - Added `swap_with_alternative` and `swap_with_alternative_owned` methods to replace primary with alternative
  - Added `replace_alternatives_with_first` and `replace_alternatives_with_first_owned` methods
  - Updated tests and documentation for new methods
  - Improved consistency with Rust's ownership patterns

## [0.5.2] - 2025-03-09

### Changed - 0.5.2

- Updated docs.rs configuration to use `all-features = true` for more standard feature documentation

## [0.5.1] - 2025-03-09

### Added - 0.5.1

- Added `From`/`Into` implementation for `Id` type
- Added implementations of `Semigroup`, `Monoid`, `Foldable`, and `Composable` traits for `Id` type
- Added configuration for docs.rs to display documentation for all features (`full`)

## [0.5.0] - 2025-03-09

### Added - 0.5.0

- Added Wrapper Type: `boxed_fn`, `first`, `last`, `product`, `sum`, `value`, `thunk`, `min`, `max`
- Added Utilities: `hkt_utils`, `transform_utils`
- Added implementations of functional traits for standard library types (`Option`, `Result`, `Vec`)
- Added ownership-based methods to traits (`fmap_owned`, `bind_owned`, `join_owned`, etc.)
- Added feature flags for customizing imports: `async`, `advanced`, `transformers`, and `full`

## [0.4.0] - 2025-02-26

### Added - 0.4.0

- Implemented `StateT` with `get`/`put`/`modify`, `bind_with`/`fmap_with`, type aliases (`StateValueMapper`, `StateCombiner`), tests, and usage documentation.
- Added `Alternative`, `Distributive`, `Divisible`, `Iso`, `NaturalTransform`, and `Representable` traits.

### Changed - 0.4.0

- Optimized `Choice` with `Arc`-based shared structure, reducing internal cloning and updating related methods, docs, and examples.

## [0.3.2] - 2025-02-18

### Added - 0.3.2

- New `Choice` data type for alternative computations
- Property-based tests for category laws
  - Added tests for Applicative laws (identity, composition, homomorphism, interchange, naturality)
  - Added tests for Bifunctor laws (identity, composition)

### Changed - 0.3.2

- Reorganized project structure
  - Renamed `monads` directory to `datatypes` for better organization
  - Renamed `category` directory to `traits` for better organization

## [0.3.1] - 2025-02-13

### Changed - 0.3.1

- Modified `lift2` and `lift3` to accept tuples for function types.
- Modified category Morphism definitions.
- Modified Free monad to be work in progress.
- Refactored FnType methods into FnTrait and added documentation.

### Removed - 0.3.1

- Removed unnecessary function types.

## [0.3.0] - 2025-02-10

### Added - 0.3.0

- Implemented Free Monad
- Integrated SendSyncFn, SendSyncFnTrait, ContravariantFn, ExtendFn, MonadFn, and ApplyFn with FnType and FnTrait
- Implemented Arrow and Category
