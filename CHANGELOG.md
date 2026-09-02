# CHANGELOG

## [Unreleased]

### Documentation Correctness

- Corrected `Max<T>::empty()` documentation: the monoid identity is
  `Max(T::default())`, and the monoid identity laws hold only when
  `T::default()` is the minimum value of `T` (e.g., unsigned integers).
  The previous claim that `T::default()` is "typically MIN_INT" was false;
  callers needing a lawful identity over signed types must use
  `Max(T::MIN)` directly.
- Documented the same limitation more precisely for `Min<T>`: the identity
  must be the maximum value of `T`, so the monoid laws do not hold with
  `T::default()` for any standard numeric type, including unsigned integers.
  Use `Min(T::MAX)` explicitly.

### Tests

- Added `test_max_min_identity_law_boundary` regression test pinning both
  the lawful cases (`Max<u32>` with default identity, explicit extremum
  identities) and the documented violations (`Max(-1)`, `Min(1)` over signed
  and unsigned integers) so the boundary behavior stays visible.

### Changed

- Generalized `pipeline_result` to accept any `IntoIterator<Item = Func>`
  instead of `Vec<Func>`, matching `pipeline_option`. Passing a `Vec`
  continues to work.

### CI/CD and Security

- Added least-privilege workflow permissions, pinned external actions, and
  workflow security checks with `actionlint` and `zizmor`.
- Declared the minimum supported Rust version through Cargo's
  `package.rust-version` metadata and added a dedicated MSRV check.
- Hardened releases with locked packaging, exact CHANGELOG validation, a
  protected crates.io environment, and verified SLSA verifier downloads.
- Added trusted benchmark regression reporting with a 20% slowdown threshold
  while keeping pull request benchmark jobs read-only.
- Added repository ownership, security reporting, pull request, and issue
  templates under `.github/`.

### Breaking Changes

- **Transformer State and Type Invariants**
  - `ReaderT<E, M, A>` now requires `M: HKT<Source = A>` and type-changing operations return the corresponding `M::Output<B>`; the unsafe bind conversion was removed.
  - `StateT<S, M, A>` now has one executable representation, requires `M: HKT<Source = (S, A)>`, and threads state left-to-right through composition.
  - `StateT` no longer exposes `Pure` or `LiftM`; its `MonadTransformer::BaseMonad` is the base family containing `A` rather than `(S, A)`.

- **Error and Conversion API**
  - Removed impossible `ChoiceError::EmptyChoice`, `PVecError::InvalidRange`, and `IOError::ValueNotSet` variants.
  - Removed `ErrorOps`, `sequence`, `traverse`, and redundant free error-conversion functions in favor of `Result`/`Iterator` methods and `From`.
  - `Validated` now converts from owned or borrowed `Result` through `From`; lossy conversion is explicitly named `into_result_first_error`.
  - Removed the panicking `NonEmptyErrors` `FromIterator` implementation; use `NonEmptyErrors::try_from_iter`, which returns `Option` for empty-capable input.
  - Removed panicking `Choice` conversions from `Vec`, slices, and iterators. Use `Choice::of_many` for an `Option` result or `TryFrom` for `Result<Choice<T>, ChoiceError>`; empty input returns `ChoiceError::EmptyInput`.

- **Dead Utilities Removed**
  - Removed empty `utils::categorical_utils`, the `utils::functions::id` alias, and unused `ReaderCombineFn`/`ContFn` aliases.

- **Duplicate Functional Data Types Removed**
  - Removed `Maybe<T>` in favor of standard `Option<T>` (`Functor`, `Applicative`, `Monad`, `Foldable` remain implemented for `Option<T>`).
  - Removed `Either<L, R>`, `EitherError`, `ResultEitherIso`, and all `Either` conversion helpers in favor of standard `Result<R, L>` or the external `either` crate.

- **Single-Implementation Traits Removed**
  - Removed `Category` and `Arrow` traits; `FunctionCategory` now provides all morphism operations via inherent associated functions (`identity_morphism`, `compose_morphisms`, `arrow`, `first`, `second`, `split`, `combine_morphisms`). Category macros (`function!`, `compose!`, `pipe!`) no longer require trait imports.
  - Removed `Comonad` trait; `Id<T>` now provides `extract`, `duplicate`, and `extend` as inherent methods.
  - Removed `Evaluate` and `EvaluateExt` traits; `Thunk` and `IO` expose their evaluation methods inherently (`Thunk::evaluate`, `IO::run`).

- **Redundant Wrappers & Pipelines Removed**
  - Removed `ErrorPipeline` and `error_pipeline` in favor of standard `Result` combinators.
  - Removed `ErrorCategory` trait; use `Result` and `Validated` directly.
  - Removed `Pipeline<T>` from `rustica::utils::transform_utils`.
  - Removed `Memoizer` wrapper; use dedicated caching crates (`lru`, `moka`).

- **Collection Iterator Helpers Removed**
  - Removed `PersistentVector::take` and `PersistentVector::skip`; use standard iterator adapters (`.iter().take(n)...`) or `PersistentVector::split_at`.

### Maintenance

- Added central compile-fail removal contract doctests in `src/lib.rs`.
- Updated all doc examples and benchmarks to 0.14.0 API.
- Persistent vectors derive length from their representation and compare/hash by logical element sequence; the unused generation counter was removed.
- Added a targeted Miri CI test for owning `ReaderT::bind` values and removed redundant phantom fields and the unused futures `thread-pool` feature.

## [0.13.0]

### Maintenance - 0.13.0

- Relaxed owned error-conversion helpers to accept non-`Clone` values.
- Simplified `Result` sequencing and pipelines with standard iterator combinators.
- Kept `ErrorPipeline` behavior unchanged in 0.13.0; migrate to native
  `Result` combinators before its planned 0.14.0 removal.

### Breaking Changes - 0.13.0

- **`Choice<T>` Impossible-State Elimination**
  - Redesigned `Choice<T>` as `{ primary: T, alternatives: SmallVec<[T; 7]> }` to guarantee at compile-time that empty choices are impossible.
  - `Choice::first(&self) -> &T` returns a direct reference without returning `Option`.
  - Removed `Choice::new_empty()`. Added `Choice::single()`, `Choice::of_many()` (returns `Option<Choice<T>>`), and `Choice::filter_values()`.
  - Implemented `Pure`, `Functor`, `Applicative`, `Monad`, `Semigroup`, `IntoIterator`, `Foldable` on `Choice<T>`.

- **`NonEmptyErrors<E>` Invariant Preservation**
  - Removed `NonEmptyErrors::remove()` to guarantee that error collections cannot be mutated into an empty state.

- **Dead Code and Speculative Helpers Removed**
  - Removed 0-impl trait `Traversable`.
  - Removed dead utility functions: `const_fn`, `compose`, `pipe`, `flip`, `fold_with`, `bimap_result`, `fan_out`, `compose_all`, `lift_option`, `transform_all`.
  - Re-exported `id` directly from `std::convert::identity`.

- **Deprecations (0.14.0 Complete Removal Notice)**
  - `Maybe<T>`: Deprecated in favor of standard `Option<T>`.
  - `Either<L, R>`: Deprecated in favor of `Result<R, L>` or the `either` crate.
  - 1-impl traits: `Comonad`, `Arrow`, `Category`, `Evaluate`, `EvaluateExt`.
  - Speculative wrappers: `ErrorCategory`, `ErrorPipeline`, `Pipeline<T>`, `Memoizer`.
  - Redundant collection iterators: `PersistentVector::{take, skip}`.

- **`Validated<E, A>` Non-Empty Error Invariant**
  - `Validated::Invalid` now stores `NonEmptyErrors<E>` instead of the public
    `ErrorVec<E>` alias, so an invalid value cannot contain zero errors.
  - `Validated::invalid_many` rejects empty input; use
    `Validated::try_invalid_many` when empty input is expected.
  - Empty invalid error arrays are rejected during serde deserialization while
    the existing JSON array representation remains unchanged.
  - Removed `Validated::invalid_vec` and `Validated::error_buffer_mut`.

- **Legacy and Redundant APIs Removed**
  - Removed legacy `Choice` alternative mutation/iteration helpers and
    `PersistentVector` cache-policy constructors.
  - Removed `ResultExt`, `try_pipeline`, `compose_when`, and the
    stdlib-equivalent categorical collection helpers. Use the documented
    conversion functions and standard `Option`/`Result`/`Iterator` APIs.
  - Removed `SemigroupExtAdapter` and `combine_all_owned`.

- **Semigroup Repetition Contract**
  - `SemigroupExt::combine_n` and `combine_n_owned` now require
    `NonZeroUsize`, eliminating the zero-count state.

### Changed - 0.13.0

- **Ownership and Allocation Paths**
  - Removed all confirmed redundant clones across library, examples, benches,
    and tests; strict `clippy::redundant_clone` now passes for all targets.
  - `FoldableExt::to_vec` now appends into one accumulator instead of cloning a
    growing `Vec`, reducing the operation from O(n²) to O(n).
  - `PersistentVector` builds owned trees leaf-by-leaf, reuses one recursive
    tree builder for owned and cloned inputs, and moves uniquely owned leaves
    during consuming conversion.
  - Vec and Choice applicative operations write directly into their final
    collection instead of creating intermediate Cartesian-product buffers.
  - Error-chain display writes directly to the formatter, and panic payloads
    containing owned `String`s are moved instead of cloned.

- **Callback and Memoizer API Boundaries**
  - `ReaderT`/`StateT` callback adapters borrow `dyn Fn` callbacks, avoiding
    per-call `Box`/`Arc` allocation; `ReaderT::lift2` returns an opaque callable.
  - Memoizer insertion now returns the named `InsertOutcome` internally and
    replaces values by move. `V: Clone` is limited to APIs that return owned
    cached copies; zero-capacity caches remain disabled.

- **Validated Error Accumulation Refactor**
  - Applicative, Bifunctor, Semigroup, sequence, collection, and traversal
    paths now share one internal `ErrorAccumulator` boundary.
  - Error order and accumulation semantics are preserved; redundant direct
    `SmallVec` construction was removed.
  - `traverse_validated` no longer requires `E: Clone`.

- **Memoizer Result Shape**
  - Eviction helpers now return the named `InsertOutcome<K, V>` structure with
    `replaced` and atomic `evicted: Option<(K, V)>` fields.

- **Iterator and Runtime Simplification**
  - Single-value `Either` and `Validated` iterators use `Option::IntoIter`.
  - Tokio runtime initialization uses `std::sync::LazyLock` instead of
    `lazy_static`.
  - `rayon` and `lazy_static` are no longer normal runtime dependencies;
    `quickcheck` is optional and `serde_json` is dev-only.

### Fixed - 0.13.0

- Fixed owned semigroup repetition that could duplicate the accumulated value
  during repeated combination.
- Fixed owned `Validated` error conversion so a singleton error is handled
  without an invalid removal operation.

See [MIGRATION_v0.13.0.md](MIGRATION_v0.13.0.md) for migration details.

## [0.12.0]

### Breaking Changes - 0.12.0

- **`Choice<T>` Typeclass Cleanup**
  - Removed deprecated methods and functions

## [0.11.1]

### Added - 0.11.1

- **`Lens<S, A>` Composition Methods**
  - Added `compose()` method for composing two lenses to access nested structures
  - Added `then()` method as a fluent alias for `compose()`
  - Enables type-safe, composable access to deeply nested data structures
  - Example: `address_lens.compose(street_lens)` creates a lens from Person to street

- **`Prism<S, A>` Composition Methods**
  - Added `compose()` method for composing two prisms to access nested sum types
  - Added `then()` method as a fluent alias for `compose()`
  - Enables type-safe, composable access to deeply nested enum variants
  - Example: `outer_prism.compose(inner_prism)` creates a prism from Outer to inner value

### Performance Optimizations

- **`Validated<E, A>` SmallVec Capacity Reduced**
  - Reduced inline capacity from `SmallVec<[E; 8]>` to `SmallVec<[E; 4]>` for better memory efficiency
  - Change affects error storage in `Validated::Invalid` variant
  - Maintains performance for common validation scenarios with fewer errors
  - Reduces stack memory usage by 50% for error collections

### Fixed - 0.11.1

- **Memoizer::with_capacity(0) Behavior**
  - Fixed to match documentation: zero capacity now creates a disabled cache
  - Previously incorrectly created an unbounded cache

## [0.11.0]

### Breaking Changes - 0.11.0

- **`utils::hkt_utils::map_result` Consolidated**
  - `map_result` function in `hkt_utils` module has been removed and consolidated into `categorical_utils`
  - `hkt_utils::map_result` now re-exports from `categorical_utils::map_result` for backward compatibility
  - Migration: No changes needed if importing from `hkt_utils`; for direct use, prefer `categorical_utils::map_result`
  - Note: `categorical_utils::map_result` uses `FnOnce` (more flexible) instead of `Fn`

- **`Validated<E, A>` Typeclass Cleanup**
  - **Removed `Monoid` implementation**: No lawful identity element exists for error-accumulating validation
    - Migration: Use `Validated::valid(...)` for domain-specific neutral values, or model error collections separately
  - **Removed `AsRef<A>` implementation**: Previous impl panicked on `Invalid`, violating `AsRef`'s total conversion contract
    - Migration: Use `Validated::as_ref()` (returns `Option<&A>`) or pattern matching
  - Removed `MonadPlus` and `Alternative` to avoid mixing fail-fast monadic semantics with error accumulation
    - Recommended helpers: `recover_all`, `recover_all_at_once`, `sequence_owned`

- **`Either<L, R>` Typeclass Cleanup**
  - **Removed `MonadPlus` implementation**: Use `Alternative` for left-biased/right-biased choice semantics

- **`Choice<T>` Typeclass Cleanup**
  - **Removed `MonadPlus` implementation**: Duplicated `Alternative` semantics (`mzero`/`mplus`)
    - Migration:
      - `<Choice<T> as MonadPlus>::mzero()` → `<Choice<T> as Alternative>::empty_alt()`
      - `a.mplus(&b)` → `a.alt(&b)`
  - `Foldable` for `Choice<T>` no longer requires `T: Clone`

- **`utils::error_utils` Module Removed**
  - All error utilities (`WithError`, `ResultExt`, `sequence`, `traverse`, etc.) moved to `crate::error`
  - Migration: `rustica::utils::error_utils::*` → `rustica::error::*` (or `rustica::prelude::error::*`)

- **Identity Trait and Implementations**
  - Fully removed the deprecated `Identity` trait and its module (`traits::identity`)
  - Deleted all `Identity` implementations on core datatypes and wrappers (`Id`, `Maybe`, `Either`, `Validated`, `Choice`, `PersistentVector`, `First`, `Last`, `Max`, `Min`, `Product`, `Sum`, `Writer`)

- **Legacy `AppError` Utilities**
  - Removed `utils::error_utils::AppError`, `error()`, and `error_with_context()` after a deprecation cycle
  - All public error construction is now routed through `crate::error::ComposableError` and its context helpers

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
  - `try_remove_alternative()` now returns `Result<Self, ChoiceError>` instead of `Result<Self, &'static str>`
  - `try_flatten()` now returns `Result<Choice<I>, ChoiceError>` instead of `Result<Choice<I>, &'static str>`
  - `try_swap_with_alternative()` now returns `Result<Self, ChoiceError>` instead of `Result<Self, &'static str>`
  - New safe method `try_first()` returns `Result<&T, ChoiceError>` instead of panicking
  - Migration: Update error handling to use `ChoiceError` enum variants

- **`Either<L, R>` Safe Methods Added**
  - `try_unwrap_left()` returns `Result<L, EitherError>` - safe alternative to `unwrap_left()`
  - `try_unwrap_right()` returns `Result<R, EitherError>` - safe alternative to `unwrap_right()`
  - `try_left_ref()` returns `Result<&L, EitherError>` - safe alternative to `left_ref()`
  - `try_right_ref()` returns `Result<&R, EitherError>` - safe alternative to `right_ref()`

- **`Validated<E, A>` Safe Methods Added**
  - `try_unwrap()` returns `Result<A, ValidatedError>` - safe alternative to `unwrap_owned()`
  - `try_unwrap_invalid()` returns `Result<SmallVec<[E; 8]>, ValidatedError>` - safe alternative to `unwrap_invalid_owned()`
  - `try_valid_ref()` returns `Result<&A, ValidatedError>` - safe reference access

- **New Error Types in `datatypes::error`**
  - `ChoiceError` - Structured errors for Choice operations (NoAlternatives, IndexOutOfBounds, EmptyPrimaryIterator, EmptyChoice)
  - `EitherError` - Structured errors for Either operations (ExpectedLeft, ExpectedRight)
  - `ValidatedError` - Structured errors for Validated operations (ExpectedValid, ExpectedInvalid)

- **Unused Trait Modules Removed**
  - Removed `contravariant_functor` - Unused contravariant functor implementation
  - Removed `natural_transformation` - Unused natural transformation trait
  - Removed `profunctor` - Unused profunctorial abstractions
  - Removed `representable` - Unused representable functor trait
  - These modules were placeholder implementations without actual use in the codebase

- **`Validated<E, A>` Performance and API Improvements**
  - **Iterator Type Consistency**: `iter_errors()` now returns `ErrorsIter` type, matching `iter_errors_mut()`
  - **Removed Unnecessary Clone Bounds**:
    - `collect()` and `collect_owned()` no longer require `C: Clone` - only `C: FromIterator<A>`
    - Improves flexibility when collecting into types that don't need Clone
  - **Performance Optimizations**:
    - `Semigroup::combine` and `Applicative::apply` optimized by removing `chain().cloned()` overhead
    - Direct `extend()` calls reduce iterator object creation
  - **New Option Conversion Methods**:
    - `as_option()` - Returns `Option<&A>` without cloning (zero-copy reference access)
    - `into_option()` - Consumes `self` and returns `Option<A>` without cloning
    - Existing `to_option()` preserved for backward compatibility (requires `A: Clone`)
  - **Async Owned Methods Added** (more efficient alternatives to reference-based async methods):
    - `fmap_valid_async_owned()` - Maps async function over valid value, consuming `self`
    - `fmap_invalid_async_owned()` - Maps async function over errors, consuming `self`
    - `and_then_async_owned()` - Chains async validation, consuming `self`
    - All owned versions avoid unnecessary cloning and use `FnOnce` bounds

- **`PersistentVector<T>` Performance and API Improvements**
  - **Iterator O(n) optimization**: Rewrote `PersistentVectorIter` with stack-based tree traversal, reducing full iteration complexity from O(n log n) to O(n)
  - **`fold_right` optimization**: Now uses `DoubleEndedIterator` instead of reverse index loop
  - **Relaxed Clone bounds**: The following operations no longer require `T: Clone`:
    - `get()`
    - `Index<usize>` trait
    - `iter()` / `IntoIterator for &PersistentVector<T>`
    - `Foldable` trait implementation
  - **DoubleEndedIterator**: Full bidirectional iteration support with independent front/back cursors for efficient `.rev()` chains

- **`Memoizer` Improvements**
  - **LRU (Least Recently Used) Eviction Policy**: Added bounded cache support with automatic eviction
    - `with_capacity(max)` - Creates a bounded LRU cache
    - Automatic eviction of least recently used entries when capacity is reached
    - O(1) access and eviction time complexity
  - **Cache Statistics**: Added performance monitoring
    - `stats()` - Returns `CacheStats` with hits, misses, evictions count
    - `hit_rate()` - Calculates cache hit ratio
    - `reset_stats()` - Resets statistics counters
    - `max_capacity()` - Returns configured maximum capacity
  - **Extended Functionality**:
    - `insert()` / `try_insert()` - Manual cache insertion without computation
    - `get_or_try_compute()` - Fallible computation support with error propagation
    - `touch()` / `try_touch()` - Update LRU position without retrieving value
  - **Safe Error Handling**: Added `MemoizerError` type and `try_*` methods that return `Result<V, MemoizerError>` instead of panicking on lock poisoning
  - **New Utility Methods**: Added comprehensive cache management methods:
    - `len()` / `try_len()` - Returns number of cached entries
    - `is_empty()` / `try_is_empty()` - Checks if cache is empty
    - `contains_key()` / `try_contains_key()` - Tests for key presence
    - `remove()` / `try_remove()` - Removes specific entry
    - `get()` / `try_get()` - Lookup without computation (does not update LRU)
    - `reserve()` / `try_reserve()` - Pre-allocates capacity
    - `shrink_to_fit()` / `try_shrink_to_fit()` - Optimizes memory usage
    - `keys()` / `try_keys()` - Returns all cached keys
    - `values()` / `try_values()` - Returns all cached values
    - `capacity()` / `try_capacity()` - Returns HashMap capacity
    - `clear()` / `try_clear()` - Clears all cached entries
  - **Bug Fixes**:
    - Fixed `get_or_compute_optimistic` to properly return cached value when another thread inserts during computation (previously returned computed value even if different from cached value)
    - Fixed capacity 0 behavior to properly disable cache (previously allowed first entry)
    - Improved documentation clarity for `get()` vs `peek()` semantics to avoid confusion about LRU updates

## [0.10.2]

### Deprecated - 0.10.2

- **`Choice<T>` Utility Methods**
  - Deprecated numerous utility methods that are not core categorical operations
  - All deprecated methods will be removed in v0.12.0
  - **Deprecated methods:**
    - `has_alternatives()` - Use `!alternatives().is_empty()` instead
    - `to_vec()` - Use `Into::<Vec<T>>::into()` or `.iter().cloned().collect()` instead
    - `find_first()` - Use `iter().find()` directly instead
    - `dedup()` - Use external iteration patterns instead
    - `dedup_by_key()` - Use external iteration patterns instead
    - `fold()` - Use the Foldable trait's `fold_left`/`fold_right` instead
    - `to_map_with_key()` - Use `iter().map().collect()` patterns instead
    - `add_alternatives()` - Use `Semigroup::combine()` or Monoid operations instead
    - `remove_alternative()` - Use `filter_values()` instead
    - `try_remove_alternative()` - Use `filter_values()` instead
    - `filter()` - Semantically unclear, use `filter_values()` instead
    - `fmap_alternatives()` - Use `fmap()` with conditional logic or external iteration instead
    - `flatten_sorted()` - Use `flatten()` then sort externally instead
    - `iter_alternatives()` - Use `alternatives().iter()` instead
    - `swap_with_alternative()` - Use external patterns instead
    - `try_swap_with_alternative()` - Use external patterns instead
    - `bind_lazy()` - Use `bind()` with `into_iter()` or flat_map patterns instead
- **Legacy Error Utilities (`utils::error_utils`)**
  - Deprecated legacy error conversion helpers in favor of the unified `src/error` module:
    - `result_to_either()` -> `crate::error::result_to_either()`
    - `either_to_result()` -> `crate::error::either_to_result()`
  - Deprecated `ResultExt` helper methods in favor of composable error operations:
    - `ResultExt::to_validated()` -> `crate::error::result_to_validated()`
    - `ResultExt::to_either()` -> `crate::error::result_to_either()`
    - `ResultExt::bimap()` -> `crate::error::ErrorOps::bimap_result()`
  - Deprecated `AppError` and its constructors in favor of `ComposableError` and the `src/error` context utilities:
    - `AppError<M, C>` -> `crate::error::ComposableError<E>` and context helpers
    - `error()` / `error_with_context()` -> `ComposableError::new(...).with_context(...)`

### Breaking Changes - 0.10.2

- **Composable Error Helpers Replace `AppError` in Core Datatypes/Transformers**
  - `State`, `Maybe`, `IO`, `ReaderT`, and `StateT` `try_*` helpers now return `ComposableResult` and emit `ComposableError`
  - Legacy `AppError` return types, constructor usages, and docs/examples were removed; context stacks now compare as `Vec<String>`
  - Tests and doctests referencing the helpers were updated to the new API, so downstream crates must migrate to `ComposableError` accessors (`core_error()`, `context()`)
- **`src/error` Module API Changes**
  - **Removed**: `with_context_result_boxed()` function - use `with_context_result()` instead
  - Function was redundant and provided no additional functionality over the standard version
  - **Changed**: `ErrorPipeline::finish()` now returns `Result<T, Box<ComposableError<E>>>`
  - Previous return type: `Result<T, ComposableError<E>>` caused large Result warnings
  - This change enables deep pipeline buffering optimization while avoiding stack overflow risks
- **`Validated` Error Handling API Changes**
  - **Removed**: `ErrorOps` implementation for `Validated` in `src/error/core.rs`
  - **Reason**: `ErrorOps::recover` is incompatible with error accumulation semantics
  - **Replacement**: Use `recover_all` or `recover_all_at_once` in `src/datatypes/validated/core.rs`

### Changed - 0.10.2

- **`Choice<T>` Refocused on Core Categorical Operations**
  - Simplified API to focus on essential Functor/Applicative/Monad/MonadPlus operations
  - Core operations retained: `new`, `new_empty`, `first`, `alternatives`, `len`, `is_empty`, `filter_values`, `flatten`, `try_flatten`, `of_many`, `iter`, and all trait implementations
  - Utility methods deprecated to reduce API surface and improve categorical clarity
- **`Choice<T>` Memory Management Optimization**
  - Removed `Arc` wrapper from `Choice<T>` internal structure
  - Changed from `Arc<SmallVec<[T; 8]>>` to `SmallVec<[T; 8]>` for direct ownership
  - Eliminated unnecessary reference counting overhead and indirection
  - Improved performance for common operations (filter, map, bind)
  - Reduced memory overhead by ~40% for small choices (≤8 items)
  - Transitioned to value semantics with explicit ownership management
  - Simplified internal implementation by removing broken Arc::try_unwrap optimization attempts
  - All operations now use direct SmallVec manipulation instead of copy-on-write patterns
  - Stack-allocated storage for small collections (≤8 items) provides excellent cache locality
- **`AsyncM` Performance Optimization**
  - Implemented **Pure Fast Path** optimization inspired by Cats Effect and ZIO
  - Added **Ultra-Fast Path** for Pure+Pure combinations (apply, zip_with)
  - Applied aggressive inlining (`#[inline(always)]`) to hot path methods
  - Introduced specialized `AsyncMInner` enum to distinguish Pure vs Lazy values
  - Reduced Arc cloning overhead by early-return pattern matching
  - Optimized methods: `fmap`, `bind`, `apply`, `zip_with` with specialized paths
  - Eliminated redundant pattern matching in Lazy-only execution paths
- **`IO` Changes**
  - **Breaking Change**: Fixed `apply` method to follow correct Applicative pattern: `IO<A>.apply(IO<Fn(A) -> B>) -> IO<B>`
  - Previously incorrect: `IO<A>.apply(Fn(A) -> IO<B>)` (was just an alias for `bind`)
  - Implemented **Pure+Pure Ultra-Fast Path** optimization inspired by AsyncM
  - Applied aggressive inlining (`#[inline(always)]`) to all hot path methods
  - Added specialized fast paths for mixed Pure/Effect combinations
  - Optimized methods: `new`, `run`, `pure`, `fmap`, `bind`, `apply`, `is_pure`, `is_effect`
  - Added comprehensive benchmarks for Pure vs Effect performance comparison
- **`src/error` Module Performance Optimization**
  - **ErrorPipeline Zero-Cost Optimization**: Removed closure overhead in `with_context()` method
  - **Direct Pattern Matching**: Replaced `map_err(|e| with_context(e, context))` with inline match expressions
  - **Deep Pipeline Buffering**: Revolutionary context buffering for performance improvement
    - **Before**: Each `with_context()` call immediately transformed `Result<T, E>` → `Result<T, ComposableError<E>>`
    - **After**: Contexts are buffered in `SmallVec<[String; 4]>` without type transformation
    - **Breaking Change**: `finish()` now returns `Result<T, Box<ComposableError<E>>>` to avoid large Result types
    - **API Compatibility**: All pipeline operations (`map`, `and_then`, `recover`, `map_error`) preserve buffered contexts
  - **Unified Context Interface**: Standardized all context functions to use `Into<String>` trait
  - **ComposableError Context Storage**: Maintained O(1) push performance with `push()` instead of `insert(0, x)`
  - **Backward Compatible API**: Preserved "most recent first" context ordering for existing code
  - **Enhanced Error Handling**: Maintained categorical correctness while improving practical performance
- **`Validated` Error Accumulation Optimizations**
  - Introduced reusable `ErrorAccumulator` helper backed by `SmallVec<[E; 8]>` for predictable, inline buffering
  - Added owned variants of the hottest APIs (`combine_errors_owned`, `sequence_owned`, `collect_owned`) to eliminate redundant cloning when ownership is available
  - Exposed zero-copy accessors (`error_slice`, `error_buffer_mut`) and iterator improvements for ergonomics without `Clone` bounds
  - Expanded documentation to describe the new borrowed vs owned API split and added regression tests covering the new helpers

## [0.10.1]

### Breaking Changes - 0.10.1

- **Identity Trait Deprecation**
  - Deprecated `Identity` trait due to design flaws
  - Removed `Functor: Identity` dependency - now `Functor: HKT`
  - Moved `id()` function from `Identity` trait to `utils::functions`
  - Added comprehensive migration guide `MIGRATION_v0.11.0.md`

### Added - 0.10.1

- **Function Utilities**
  - Added `utils::functions` module with fundamental FP utilities
  - Added `id()` - identity function (category theory morphism)
  - Added `const_fn()` - create constant functions
- **Documentation**
  - Added documentation for `PersistentVector` methods and types
  - Added `pipe` function to `utils::transform_utils`
  - Added comprehensive migration guide for breaking changes
- **Enhanced IO Monad Error Handling**
  - Integrated `src/error` module's unified error handling system with IO monad
  - Added `try_get_composable()` - returns `ComposableResult<A, IOError>` with rich error context
  - Added `try_get_composable_with_context()` - adds contextual information to errors
  - Added `into_error_pipeline()` - enables functional error handling chains
  - Added `recover()` - provides error recovery with custom fallback logic
  - Added `recover_with()` - simple default value fallback on failure
  - Added `sequence_composable()` - collects all errors instead of failing fast
- **Error Context Accumulation**
  - IO errors now support context stacking with `ComposableError`
  - Error chains provide full trace of operation context
  - Context information is preserved through IO operations
- **Functional Error Composition**
  - ErrorPipeline integration for complex error handling chains
  - Type-safe error transformations after Result extraction
  - Backward compatibility with existing `try_get()` method

### Changed - 0.10.1

- **IO Error Semantics**
  - Enhanced error documentation with ComposableError patterns
  - Improved error recovery patterns and best practices
  - Updated Quick Start examples with new error handling features

### Fixed - 0.10.1

- **Category Theory Compliance**
  - Fixed Functor to properly extend only HKT (not Identity)
  - Improved separation of concerns between value extraction and functor operations
- **compose function order**
  - Fixed compose function order in tests
- **Error Handling Doctests**
  - Fixed doctest failures in `map_error` method by removing problematic methods
  - Improved error handling examples and documentation

### Deprecated - 0.10.1

- **Identity Trait**
  - `Identity` trait is deprecated and will be removed in v0.12.0
  - Use standard methods (`unwrap()`, `as_ref()`) or `Comonad::extract()` instead

## [0.10.0]

### Added - 0.10.0

- **Wrapper From/Into trait implementation**
  - Added `From<T>` and `Into<T>` implementations for wrapper types:
    - `Sum<T>`: `From<T>` implementation for direct value wrapping
    - `Product<T>`: `From<T>` implementation for direct value wrapping
    - `First<T>`: `From<Option<T>>` implementations for optional initialization
    - `Last<T>`: `From<Option<T>>` implementations for optional initialization
    - `Min<T>`: `From<T>` implementation for direct value wrapping
    - `Max<T>`: `From<T>` implementation for direct value wrapping
    - `Value<T>`: `From<T>` implementation for seamless conversion from any value
- **Monoid utility function**
  - Added `fold_with` utility function for folding iterators into monoid wrappers using `From<T>` trait
  - Provides efficient folding with automatic conversion from item type to wrapper type
  - Uses the first element as initial value and `Monoid::empty()` for empty iterators
- **Function Category implementation**
  - Added `FunctionCategory` struct implementing both `Category` and `Arrow` traits
  - Provides concrete implementation of category theory for Rust functions

### Changed - 0.10.0

- **Category trait inheritance removed from HKT**
  - `Category` now focuses purely on morphism composition without HKT dependencies
  - `HKT` remains independent for type constructor operations
- **Increased default stack size for `Validated` from 4 to 8 elements**
  - This change reduces heap allocations and improves performance
- **Change and simplify `PersistentVector`**
  - [BREAKING CHANGE] removed `with_cache_policy` and `from_slice_with_cache_policy`
  - [BREAKING CHANGE] removed `with_chunk_size` and chunk size is now fixed at 64
  - [BREAKING CHANGE] removed `ChunkIter`
  - [BREAKING CHANGE] removed `pvec` feature flag
  - Simplified `PersistentVector` API by removing cache policy and chunk size
- **MSRV updated to 1.88.0**

### Removed - 0.10.0

- [BREAKING CHANGE] **remove `Foldable` trait impl in monoid wrappers**
- [BREAKING CHANGE] **remove `Composable` trait**
- [BREAKING CHANGE] **remove `Value` wrapper**
- [BREAKING CHANGE] **remove `to_arc()` method from PersistentVector**
  - The `to_arc()` method has been removed as part of the PersistentVector API simplification
  - Users should use standard Arc wrapping if needed: `Arc::new(vector)`

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
  - Introduced `CachePolicy` trait with implementations (`AlwaysCache`, `NeverCache`, `EvenIndexCache`)
  - Added dynamic cache management APIs: `with_cache_policy`, `from_slice_with_cache_policy`, etc.
  - Comprehensive documentation and examples for custom caching strategies

### Changed - 0.6.2

- **Persistent Vector Improvements**

  - Performance & memory optimization across all core data structures
  - API & documentation refactoring for clarity and idiomatic usage
  - Implemented `Index<usize>` and `IntoIterator` for better ergonomics
  - Expanded test coverage for indexing, iteration, and edge cases

- **Error Handling Standardization**

  - Unified error handling using `AppError` from `error_utils.rs`
  - Replaced most panics with composable `Result` types
  - Added rich contextual error messages in core operations
  - Enhanced documentation for error types and propagation

- **Monoid & Comonad Enhancements**

  - Added utilities: `is_empty_monoid()`, `repeat`, `mconcat`, `power`
  - Implemented `Comonad` trait for `Option`, `Result`, and `Maybe`

- **Iso Trait Enhancements**
  - Added `ResultValidatedIso` for seamless conversion between `Result` and `Validated`
  - Converted static methods to instance methods for better composability

### Fixed - 0.6.2

- SmallVec initialization from slice now uses a loop to avoid method compatibility issues

### Refactored - 0.6.2

- Integrated `cache`, `chunk`, and `memory` modules into unified `memory.rs`
- Removed dead code and improved formatting for consistency

### IO Monad Improvements - 0.6.2

- Refactored `IO<A>`:
  - Internal implementation now uses `Arc<dyn Fn()>` with minimal value cloning for better performance and ergonomics.
  - `pure`, `delay`, `delay_efficient` now only clone values when IO is run multiple times, reducing unnecessary heap allocations.
  - `delay_efficient` now uses the `spin_sleep` crate for precise spin-based delays; `delay` continues to use `std::thread::sleep`.
  - Each method is now thoroughly documented, including tradeoffs between blocking and spinning, and async/await extension notes.
  - Doctests improved to follow Rust best practices for generics, trait imports, and error handling.
- Updated documentation to clearly explain usage, error handling, and performance tradeoffs for large IO chains.

## [0.6.1]

### Added - 0.6.1

- Small vector optimization for PersistentVector to improve memory efficiency
  - Optimized representation for vectors with 8 or fewer elements using inline storage
  - Up to 97% performance improvement for empty vector creation
  - ~5% improved performance for push operations
- Additional methods for PersistentVector
  - `pop_back` - Removes the last element and returns it with the updated vector
  - `to_arc` - Converts vector to Arc for efficient sharing across threads
- Enhanced documentation for vector operations
  - Added comprehensive doctests and examples
  - Improved API documentation with usage examples
  - Updated README with memory optimization details
- Added `par_map` method to `PersistentVector` for parallel mapping of elements using Rayon (feature: "async").

## [0.6.0]

### Added - 0.6.0

- New `pvec` module that provides persistent vector implementations with optional feature flags for memory optimization strategies
- Improved functional programming support for collection types
- New `memoize` module in `wrapper` namespace for caching function results
- Added `MemoizeFn` type to `wrapper/memoize.rs` for enhanced function memoization
- Added `MemoizeReader` type to `reader.rs` to support memoized Reader-pattern computations
- Added memory optimization for wrapper types
- Implemented `Identity` and `Functor` traits for wrapper types (`First`, `Last`, `Max`, `Min`, `Product`, `Sum`, `Value`)
- Monoid trait implementation for Min and Max wrapper types
- New documentation guides:
  - DOCTEST_GUIDELINE.md - Best practices for writing effective doctests
  - PERFORMANCE.md - Performance characteristics and optimization guidelines
  - TUTORIAL.md - Comprehensive tutorial for functional programming beginners
- `MaybeError` enum for standard Maybe unwrap errors
- `WithError` trait implementation for `Maybe<T>`
- `MaybeExt` extension trait with additional error handling methods
- `to_standard_result()` method returning `Result<T, MaybeError>`
- `try_unwrap()` method returning `Result<T, AppError>` with context
- `to_result<E>()` method for conversion with custom error types
- Comprehensive test suite for Maybe error handling
- Bidirectional conversion between `Reader` and `ReaderT` in Scala cats style:
  - `to_reader_t` method for converting `Reader<E, A>` to `ReaderT<E, M, A>`
  - `to_reader` method for converting `ReaderT<E, Id<A>, A>` back to `Reader<E, A>`
  - `from_reader` constructor for creating `ReaderT` directly from `Reader`
  - `pure` method for lifting values into `ReaderT` context

### Changed - 0.6.0

- Removed the `transformers` and `advanced` feature flag as core functionality is now included by default
- Refactored `Reader` monad to use the `ReaderT` transformer internally, improving type safety and composability
- Removed redundant `map` method from `Id` type to encourage consistent use of `fmap` across library
- Simplified `Lens` and `Prism` implementations by removing `Arc` dependency, making type inference easier
- Simplified the `Maybe` monad implementation:
  - Removed `map` method (use `fmap` from the Functor trait instead)
  - Removed `map_or_else` method (can be composed from other methods)
  - Renamed `map_or` to `fmap_or` for better naming consistency
- Renamed mapping methods in the `Either` type for better API consistency:
  - `map_left` -> `fmap_left`
  - `map_right` -> `fmap_right`
- Simplified `Choice` datatype implementation:
  - Removed duplicated methods in favor of ownership-based versions
  - Refactor `swap_with_alternative` renamed ownership-based versions to be the default, removing the `_owned` suffix
    - Removed reference-based versions in favor of the ownership-based implementations
  - Refactor `add_alternative` renamed ownership-based versions to be the default, removing the `_owned` suffix
    - Removed reference-based versions in favor of the ownership-based implementations
  - Removed less commonly used methods like `change_first`, `all_values`, `find_alternative`, and `from_iterator`
- Refactored `Maybe<T>` error handling to use standard patterns
- Improved error messages and context for debugging
- Enhanced conversions between `Maybe`, `Option`, and `Result` types
- Updated internal implementations to align with standardized error handling

### Removed - 0.6.0

- Removed `BoxedFn` wrapper type from `wrapper/boxed_fn.rs`
- Removed several specialized methods from `Choice` to streamline the API:
  - `replace_alternatives_with_first`: can be achieved with core methods
  - `with_ordered_alternatives` and `with_ordered_alternatives_owned`: specialized sorting operations
  - `with_unique_alternatives` and `with_unique_alternatives_owned`: specialized deduplication operations
  - `partition`: static method with potential panic behavior
  - `group_by`: complex categorization operation
  - `match_choice` and `match_choice_owned`: redundant with Rust's native pattern matching
  - `zip`: specialized operation for combining multiple `Choice` instances

## [0.5.4] - 2025-03-24

### Added - 0.5.4

- Implemented `StateT` monad transformer
  - Added core implementation with state manipulation functions (`get`, `put`, `modify`)
  - Added composition with other monads via `bind_with` and `fmap_with`
  - Added utility type aliases (`StateValueMapper`, `StateCombiner`) for better code organization
  - Added comprehensive tests covering state operations, error handling, and composition scenarios
  - Added detailed documentation with usage examples
- Added new functional programming traits
  - `Alternative`: For types with choice and empty implementations
  - `Distributive`: The dual of Traversable, distributing a functor over another
  - `Divisible`: Contravariant analogue of Applicative
  - `Iso`: For isomorphic type relationships
  - `NaturalTransform`: For converting between functors preserving structure
  - `Representable`: For functors that can be represented by a mapping from a key type

### Changed - 0.5.4

- Optimized `Choice` data structure:
  - Implemented shared structure optimization using `Arc` for improved memory efficiency
  - Reduced unnecessary cloning operations in internal data representation
  - Updated relevant methods to leverage the new shared structure
  - Adjusted documentation and examples to reflect the optimization changes

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

- Implemented `StateT` monad transformer
  - Added core implementation with state manipulation functions (`get`, `put`, `modify`)
  - Added composition with other monads via `bind_with` and `fmap_with`
  - Added utility type aliases (`StateValueMapper`, `StateCombiner`) for better code organization
  - Added comprehensive tests covering state operations, error handling, and composition scenarios
  - Added detailed documentation with usage examples
- Added new functional programming traits
  - `Alternative`: For types with choice and empty implementations
  - `Distributive`: The dual of Traversable, distributing a functor over another
  - `Divisible`: Contravariant analogue of Applicative
  - `Iso`: For isomorphic type relationships
  - `NaturalTransform`: For converting between functors preserving structure
  - `Representable`: For functors that can be represented by a mapping from a key type

### Changed - 0.4.0

- Optimized `Choice` data structure:
  - Implemented shared structure optimization using `Arc` for improved memory efficiency
  - Reduced unnecessary cloning operations in internal data representation
  - Updated relevant methods to leverage the new shared structure
  - Adjusted documentation and examples to reflect the optimization changes

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
