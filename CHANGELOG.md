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
