# Rustica 0.14.0 Migration Guide

This document provides a guide for migrating code from Rustica 0.13.x to 0.14.0.

Rustica 0.14.0 removes the APIs deprecated in 0.13.0 and tightens transformer and error-state invariants. These are intentional breaking changes that eliminate duplicate standard-library functionality and states that valid values could never reach.

---

## Summary of Breaking Changes

| Deprecated / Removed in 0.14.0 | Recommended Replacement |
| --- | --- |
| `Maybe<T>` | Standard `Option<T>` (`rustica::traits::Functor`, `Monad`, etc. are implemented for `Option`) |
| `Either<L, R>` | Standard `Result<R, L>` or external `either` crate |
| `EitherError` | Standard `Result` pattern matching |
| `ResultEitherIso`, `either_to_result`, etc. | Standard `Result` methods |
| `Category`, `Arrow` traits | `FunctionCategory` inherent associated functions |
| `Comonad` trait | `Id<T>` inherent methods (`extract`, `duplicate`, `extend`) |
| `Evaluate`, `EvaluateExt` traits | Inherent methods (`Thunk::evaluate`, `IO::run`) |
| `ErrorPipeline`, `error_pipeline` | Native `Result` combinators + `with_context` |
| `ErrorCategory` trait | Native `Result` and `Validated` methods |
| `Pipeline<T>` | Native method chaining on `Functor` types |
| `Memoizer` | Dedicated caching crates ([`lru`](https://crates.io/crates/lru), [`moka`](https://crates.io/crates/moka)) |
| `PersistentVector::{take, skip}` | `.iter().take(n).cloned().collect()` / `.split_at(n)` |
| `ReaderT<E, M, A>` with unrelated `M`/`A` | Use a base monad whose `HKT::Source` is `A`; mapped/bound results use `M::Output<B>` |
| `StateT::{Pure, LiftM}` | Construct executable transitions with `StateT::new`, `pure`, or `MonadTransformer::lift` |
| `ErrorOps::{recover, bimap_result}` | `Result::or_else`, followed by `map` and `map_err` |
| `error::{sequence, traverse}` | `into_iter().collect()` / `into_iter().map(f).collect()` |
| `result_to_validated` / `Validated::from_result*` | `Validated::from(result)` or `result.into()` |
| `validated_to_result` / `Validated::to_result*` | `validated.into_result_first_error()` |
| `core_to_composable` / `wrap_in_composable_result*` | `ComposableError::from` / `Result::map_err` |
| `composable_to_core` / `flatten_composable_result` | Access `ComposableError::core_error` / `Result::map_err` |
| `utils::functions::id` | `std::convert::identity` |
| Empty `utils::categorical_utils` module | Remove the import; use the standard iterator and `Result` operations directly |
| `ReaderCombineFn`, `ContFn` aliases | Use `ReaderT`/`Cont` operations directly and let closure types be inferred |
| `ChoiceError::EmptyChoice` | Remove the unreachable match arm; `Choice<T>` cannot be empty |
| `PVecError::InvalidRange` | Remove the unreachable match arm; no public operation produces this variant |
| `IOError::ValueNotSet` | Remove the unreachable match arm; executable `IO` values do not have an unset state |
| `Choice::{From<Vec<_>>, From<&[_]>, FromIterator}` | `Choice::of_many(...)` or `TryFrom` (`values.try_into()`) |
| `NonEmptyErrors::FromIterator` | `NonEmptyErrors::try_from_iter(...)` (`Option` result) |

---

## Detailed Migration Examples

### Transformer type changes

`ReaderT` and `StateT` now encode their base-monad contents in the type system. A type-changing reader map therefore changes `Option<A>` to `Option<B>`, and state-transformer composition always uses `(state, value)` internally:

```rust
use rustica::transformers::{ReaderT, StateT};

let reader: ReaderT<i32, Option<i32>, i32> = ReaderT::new(Some);
let text: ReaderT<i32, Option<String>, String> = reader.fmap(|n| n.to_string());

let state: StateT<i32, Option<(i32, i32)>, i32> =
    StateT::new(|s| Some((s + 1, s)));
let text_state: StateT<i32, Option<(i32, String)>, String> =
    state.fmap(|n| n.to_string());
```

`State<S, A>` still returns `(A, S)` publicly; tuple reordering occurs only at its `StateT` conversion boundary.

### Error conversion changes

```rust
use rustica::datatypes::validated::Validated;

let validated: Validated<&str, i32> = Result::<i32, &str>::Ok(42).into();
let result = validated.into_result_first_error();
assert_eq!(result, Ok(42));
```

Borrowed results are also supported when both payloads implement `Clone`:

```rust
use rustica::datatypes::validated::Validated;

let result = Result::<String, String>::Ok("ready".into());
let validated: Validated<String, String> = (&result).into();
assert_eq!(validated.into_result_first_error(), Ok("ready".into()));
```

Because `Validated` can accumulate multiple errors while `Result` carries only one, `into_result_first_error` deliberately returns the first error. Use `into_error_payload` when every accumulated error must be preserved.

### `Maybe<T>` → `Option<T>`

`Maybe<T>` was a duplicate of `Option<T>`. In Rustica, `Option<T>` implements all functional traits (`Functor`, `Applicative`, `Monad`, `Foldable`, `Traversable`).

#### Before (0.13.x) - Maybe

```rust
use rustica::datatypes::maybe::Maybe;
use rustica::traits::functor::Functor;

let value = Maybe::Just(42);
let doubled = value.fmap(|x| x * 2);
assert_eq!(doubled, Maybe::Just(84));

let empty: Maybe<i32> = Maybe::Nothing;
assert!(empty.is_nothing());
```

#### After (0.14.0) - Maybe

```rust
use rustica::traits::functor::Functor;

let value = Some(42);
let doubled = value.fmap(|x| x * 2);
assert_eq!(doubled, Some(84));

let empty: Option<i32> = None;
assert!(empty.is_none());
```

---

### `Either<L, R>` → `Result<R, L>`

#### Before (0.13.x) - Either

```rust
use rustica::datatypes::either::Either;
use rustica::traits::functor::Functor;

let res: Either<String, i32> = Either::Right(42);
let mapped = res.fmap(|x| x + 1);
assert_eq!(mapped, Either::Right(43));

let err: Either<String, i32> = Either::Left("failed".to_string());
```

#### After (0.14.0) - Either

```rust
use rustica::traits::functor::Functor;

let res: Result<i32, String> = Ok(42);
let mapped = res.fmap(|x| x + 1);
assert_eq!(mapped, Ok(43));

let err: Result<i32, String> = Err("failed".to_string());
```

---

### Single-Implementation Traits

#### `Category` & `Arrow` → `FunctionCategory` Inherent Methods

The `Category` and `Arrow` traits are removed. `FunctionCategory` provides all morphism methods directly, and macros (`function!`, `compose!`, `pipe!`) work without trait imports.

```rust
use rustica::category::FunctionCategory;

let id_fn = FunctionCategory::identity_morphism::<i32>();
let arrow_fn = FunctionCategory::arrow(|x: i32| x * 2);
let first_fn = FunctionCategory::first::<i32, i32, &str>(&arrow_fn);
```

#### `Comonad` → `Id` Inherent Methods

```rust
use rustica::datatypes::id::Id;

let id = Id::new(42);
assert_eq!(id.extract(), 42);
let duplicated = id.duplicate();
let extended = id.extend(|i| i.extract() * 2);
```

#### `Evaluate` → Inherent Methods

```rust
use rustica::datatypes::wrapper::thunk::Thunk;

let thunk = Thunk::new(|| 42);
assert_eq!(thunk.evaluate(), &42);
assert_eq!(thunk.evaluate_owned(), 42);
```

---

### Error Handling & Pipelines

#### `ErrorPipeline` → Native `Result` Combinators

```rust
use rustica::error::{ComposableError, with_context};

let result: Result<i32, &str> = Err("404");
let final_result = result
    .map(|x| x * 2)
    .map_err(|e| with_context(e, "Request failed"))
    .or_else(|_| Ok::<i32, ComposableError<&str>>(0));
```

---

### Non-empty collection construction

`Choice` and `NonEmptyErrors` no longer implement infallible collection conversions. Empty input previously caused a panic through `From` or `FromIterator`; use an explicit fallible API instead:

```rust
use rustica::datatypes::choice::Choice;
use rustica::datatypes::validated::NonEmptyErrors;

let choice_result: Result<Choice<i32>, _> = vec![1, 2].try_into();
let choice = Choice::of_many([1, 2]);
let errors = NonEmptyErrors::try_from_iter(["first", "second"]);
```

`Choice` conversions return `Result<Choice<T>, ChoiceError>` and report `ChoiceError::EmptyInput`; `NonEmptyErrors::try_from_iter` returns `None` for an empty iterator. Existing `Choice::of_many` and `Validated::try_invalid_many` remain available when `Option` is the desired result.

### Collections: `PersistentVector::{take, skip}`

```rust
use rustica::pvec::PersistentVector;

let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);

// Iterator approach
let taken: PersistentVector<i32> = vec.iter().take(3).cloned().collect();
let skipped: PersistentVector<i32> = vec.iter().skip(2).cloned().collect();

// Structural split approach (O(log n))
let (head, _) = vec.split_at(3);
let (_, tail) = vec.split_at(2);
```

No migration is required for equality, ordering, or hashing. In 0.14.0 these operations consistently use the vector's logical element sequence, independent of whether the values are stored inline or in the RRB tree and independent of construction history.

### `PersistentVector` concatenation and `pop_back`

`PersistentVector::concat` now preserves left-to-right operand order even when
its RRB trees have different heights. `pop_back` also continues until the
vector is empty when front insertions leave values in the head buffer after the
main tree is exhausted. No API migration is required; these are correctness
fixes to existing operations.

---

## Behavior Notes

### `Min<T>` / `Max<T>` are semigroups

In 0.14.0, `Min<T>` and `Max<T>` no longer implement `Monoid`. A generic
`T::default()` is not guaranteed to be the maximum or minimum value, so it
cannot serve as a lawful identity for every `T` admitted by the wrappers.

If you previously reduced a possibly empty collection with `empty()`, use the
`Option`-returning `combine_all_values` helper:

```rust
use rustica::datatypes::wrapper::min::Min;
use rustica::traits::semigroup::combine_all_values;

let minimum = combine_all_values([Min(4), Min(1), Min(3)]);
assert_eq!(minimum, Some(Min(1)));
```

For a domain with a known extremum, seed the reduction explicitly, for example
`Max(i32::MIN)` or `Min(i32::MAX)`. See `docs/wrapper-monoid-identity.md`.

### `Result` and `MonadPlus`

`Result<T, E>` no longer implements `MonadPlus`: `E::default()` cannot
preserve an arbitrary existing error as the right identity. Use native
`Result` combinators such as `or_else` for fallback behavior. `Option<T>`
retains its `MonadPlus` implementation when `None` is the lawful zero.

### Phantom marker wrappers

`HKTType` and `PureType` were zero-sized forwarding markers without behavior
beyond the underlying traits and are removed in 0.14. Use `HKT`/`Pure` or the
`PureExt` methods directly.

### `pipeline_result` Accepts Any Iterator

`rustica::utils::hkt_utils::pipeline_result` now takes
`impl IntoIterator<Item = Func>` instead of `Vec<Func>`, matching
`pipeline_option`. Existing `Vec` callers compile unchanged; no action is
required.
