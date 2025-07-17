# CHANGELOG

## [0.8.1]

### Added - 0.8.1

### Change - 0.8.1

### Removed - 0.8.1

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
