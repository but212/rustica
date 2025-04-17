# CHANGELOG

## [0.6.2]

### Persistent Vector Optimizations
- Major performance and memory optimizations for the persistent vector implementation:
  - Streamlined memory management for all core data structures (VectorImpl, SmallVec, Tree, Node, Chunk).
  - Fixed initialization of `[Option<T>; N]` in `SmallVec` to avoid requiring `T: Copy` and ensure safe, idiomatic Rust.
  - Improved method inlining and added `#[must_use]` to critical methods for better performance and correctness.
  - Refactored and documented all public methods for clarity and idiomatic usage.
  - Implemented `Index<usize>` and `IntoIterator` for `PersistentVector<T>` and references, enabling ergonomic indexing and iteration.
  - Optimized chunked and tree-backed operations to minimize unnecessary allocations and cloning.
  - Ensured all trait implementations and constructors have correct visibility and safety guarantees.
  - Fixed all Clippy and Rustc warnings, including redundant closures and array initialization issues.
  - Updated tests to cover all indexing, iteration, and edge cases for persistent vectors.

### Internal Refactoring
- Refactored function signatures and formatting for consistency and readability across all persistent vector modules.
- Removed or consolidated unused code paths and dead code warnings.
- Improved error handling and documentation throughout the persistent vector codebase.

### Added
- Enhanced Monoid trait with additional utility functions
  - Added `is_empty_monoid()` method to test if a value equals the identity element
  - Added `repeat(value, n)` function to create a monoid by repeating an element n times
  - Added `mconcat(values)` function to combine values from a slice
  - Added `power(value, exponent)` function to combine a monoid with itself multiple times
  - Improved documentation with comprehensive examples and doctests
- Implemented Comonad trait for standard library types
  - Added implementations for `Option<T>` and `Result<T, E>` with proper Clone bounds
  - Added doctests and examples for Comonad operations 
  - Implemented Comonad for the Maybe type with Clone semantics

### Changed
- Refactored Iso trait to use instance methods and improve composability
  - Converted static methods to instance methods with `&self` parameter
  - Implemented proper field usage in `ComposedIso` and `InverseIso` structs
  - Added `iso_compose` method for composing isomorphisms in a functional style
  - Fixed compilation issues with proper type constraints and Clone bounds
  - Updated documentation and examples to reflect instance method usage
- Refactored composition functions to build on more basic operations
  - Modified `compose_fallible` to use the basic `compose` function with Result's `and_then`
  - Modified `compose_option` to use the basic `compose` function with Option's `and_then`
  - Modified `compose_option_result` to use basic composition with transformation
  - Simplified collection operations like `compose_filter` and parallel operations to use basic composition
  - Added explanatory comments to clarify relationships between different composition functions
  - Improved modularity and maintainability through better functional composition
  
### CI/CD Improvements
- Enhanced `rust.yml` with matrix testing across multiple platforms and Rust channels
- Improved `code-quality.yml` with additional documentation checks and security audit
- Updated `create-release.yml` with cross-platform artifact building and automatic changelog generation
- Enhanced `publish-crates.yml` with version validation and duplicate publishing prevention
- Improved `benchmark.yml` with comparison reports and PR comments
- Updated `generator-generic-ossf-slsa3-publish.yml` to use latest SLSA generator (from v1.4.0 to v2.1.0)

### Refactored Node Memory Management
- **Major Refactor:** Removed all custom pooling and Drop logic from persistent vector node and chunk management. Memory management is now handled entirely by Rust's standard ownership and reference counting (Arc), greatly simplifying the codebase.
- All `ManagedRef` and node creation/manipulation APIs now use `Arc` and safe immutable references.
- Methods no longer rely on `get_mut`, pooling, or manual memory recycling.
- Pointer comparisons now use `Arc::ptr_eq` instead of deprecated or custom pointer logic.
- All chunk and node modifications are done with new allocations and cloning, following Rust's functional and ownership principles.
- Updated all relevant doctests and internal documentation to match the new memory management approach.
- **Breaking Change:** Any code relying on the previous pooling or Drop behavior must be updated to use the new API.

### Improved Encapsulation in the pvec Module
- Restricted visibility of implementation details to improve API clarity
  - Made internal components like `IndexCache`, `Chunk`, `Iterator`, `Node`, and `Tree` non-public (`pub(crate)` or `pub(super)`)
  - Restricted visibility of implementation constants (`CHUNK_SIZE`, `NODE_SIZE`, etc.)
  - Kept only necessary types public (`PersistentVector`, `MemoryManager`)
- Removed unnecessary internal methods that were no longer needed after memory management refactoring
- Simplified the public API surface while maintaining all functionality
- Updated tests to use the public API instead of internal implementation details

### Error Handling Standardization
- Standardized error handling across all persistent vector modules (`src/pvec`) using the utilities from `src/utils/error_utils.rs`.
  - Replaced all `panic!`s and ad-hoc error returns with composable `Result<T, AppError<String, String>>` or type aliases.
  - Adopted `AppError` and `error_with_context` for rich, contextual error messages.
  - Updated all core tree/node operations (`find_child_index`, `modify_branch`, `replace_child`, `split`, etc.) to propagate errors using idiomatic Rust patterns.
  - Improved documentation for error types and propagation in method comments.
  - Ensured all error handling is consistent, robust, and ready for downstream integration/testing.

## [0.6.1]

### Added
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

## [0.6.0]

### Added
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

### Changed
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

### Removed
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

### Added
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

### Changed
- Optimized `Choice` data structure:
  - Implemented shared structure optimization using `Arc` for improved memory efficiency
  - Reduced unnecessary cloning operations in internal data representation
  - Updated relevant methods to leverage the new shared structure
  - Adjusted documentation and examples to reflect the optimization changes

## [0.5.3] - 2025-03-16

### Changed
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

### Changed
- Updated docs.rs configuration to use `all-features = true` for more standard feature documentation


## [0.5.1] - 2025-03-09

### Added
- Added `From`/`Into` implementation for `Id` type
- Added implementations of `Semigroup`, `Monoid`, `Foldable`, and `Composable` traits for `Id` type
- Added configuration for docs.rs to display documentation for all features (`full`)

## [0.5.0] - 2025-03-09

### Added
- Added Wrapper Type: `boxed_fn`, `first`, `last`, `product`, `sum`, `value`, `thunk`, `min`, `max`
- Added Utilities: `hkt_utils`, `transform_utils`
- Added implementations of functional traits for standard library types (`Option`, `Result`, `Vec`)
- Added ownership-based methods to traits (`fmap_owned`, `bind_owned`, `join_owned`, etc.)
- Added feature flags for customizing imports: `async`, `advanced`, `transformers`, and `full`

## [0.4.0] - 2025-02-26

### Added
- Added tests for DataType: `test_async_monad`, `test_choice`, `test_cont`, `test_either`, `test_id`, `test_io`.

### Changed
- Removed `FnType` and `FnTrait`: Simplified function implementation and usage.
- Removed `TypeConstraints`: Simplified type constraints.
- Directly implemented types with functions as members without traits: Addressed limitations of Rust type system by handling them directly.
- Changed development direction of `Choice` type: Now provides a primary value (`first`) and alternatives (`Vec<T>`) of a single type `T`.

### Documentation
- Enhanced documentation for individual sources: Richer content viewable through [docs.rs](https://docs.rs).


## [0.3.2] - 2025-02-18

### Added
- New `Choice` data type for alternative computations
- Property-based tests for category laws
  - Added tests for Applicative laws (identity, composition, homomorphism, interchange, naturality)
  - Added tests for Bifunctor laws (identity, composition)

### Changed
- Reorganized project structure
  - Renamed `monads` directory to `datatypes` for better organization
  - Renamed `category` directory to `traits` for better organization

## [0.3.1] - 2025-02-13

### Changed
- Modified `lift2` and `lift3` to accept tuples for function types.
- Modified category Morphism definitions.
- Modified Free monad to be work in progress.
- Refactored FnType methods into FnTrait and added documentation.

### Removed
- Removed unnecessary function types.

## [0.3.0] - 2025-02-10

### Added
- Implemented Free Monad
- Integrated SendSyncFn, SendSyncFnTrait, ContravariantFn, ExtendFn, MonadFn, and ApplyFn with FnType and FnTrait
- Implemented Arrow and Category

### Changed
- Updated version to 0.3.0
