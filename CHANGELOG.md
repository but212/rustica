## [0.6.0]

### Added
- New `pvec` module that provides persistent vector implementations
- Improved functional programming support for collection types
- New `memoize` module in `wrapper` namespace for caching function results
- Added memory optimization for wrapper types
- Monoid trait implementation for Min and Max wrapper types
- New documentation guides:
  - DOCTEST_GUIDELINE.md - Best practices for writing effective doctests
  - PERFORMANCE.md - Performance characteristics and optimization guidelines
  - TUTORIAL.md - Comprehensive tutorial for functional programming beginners

### Changed
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

### Removed
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
