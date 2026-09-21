# Rustica 0.18.0 Migration Guide

This guide details all removals and breaking changes in Rustica 0.18.0, with concrete replacement patterns for each removed type, trait, and function.

---

## Quick Reference Summary

| Removed Item | Direct Replacement |
| --- | --- |
| `transformers::*` (`StateT`, `ReaderT`, `ContT`) | Native Rust control flow, `&mut S`, `&Context`, `async`/`await` |
| `datatypes::state::State` | `&mut S` parameter or closure `FnMut(&mut S) -> A` |
| `datatypes::reader::Reader` | Borrowed context `&Context` or closure `Fn(&Context) -> A` |
| `datatypes::writer::Writer` | `&mut Buffer` or `tracing` / `log` crates |
| `datatypes::cont::Cont` | Standard closures or early returns (`?`, `return`) |
| `datatypes::io::IO` | Native synchronous or asynchronous functions |
| `datatypes::id::Id` | Bare values `T` |
| `datatypes::async_monad::AsyncM` | Native `async`/`await` and `Future` |
| `datatypes::wrapper::*` (`First`, `Last`, `Min`, `Max`, `Sum`, `Product`, `Predicate`) | `Option::or`, `cmp::min`/`max`, `Iterator::sum`/`product`, closures |
| `category::*` (`FunctionCategory`, macros) | Standard closures, function composition via iterators |
| `error::ComposableError` & related types | `ContextError` (`rustica::error::ContextError`) |
| `error::WithError` & `sequence_with_error` | Standard `Result` combinators or `Iterator::collect` |
| `traits::Alternative` | `Option::or`, `Vec::extend`, `bool::then_some` |
| `traits::Bifunctor`, `BinaryHKT` | Inherent `Validated::bimap`, `map`, `map_err` |
| `Validated<E, A>` (type parameter order) | `Validated<T, E>` matching standard `Result<T, E>` |
| `Validated::map_valid` / `fmap_invalid` | `Validated::map` / `Validated::map_err` |
| `traits::Iso` | Standard `From` / `Into` conversions |
| `traits::MonadError` | `Result::or_else`, `?` operator |
| `traits::One` | Numeric literals (`1`) or `Iterator::product` |
| `Free::fold_map` | `Free::run` or `Free::try_run` with trampoline evaluation |
| `Free::into_pure` | `Free::to_pure` |
| `Lens::from_iso`, `Prism::from_iso` | `Lens::new` or `Prism::new` directly with closures |
| `Command` in `rustica::prelude::*` | Explicit import: `use rustica::datatypes::operational::Command;` |

---

## 1. Monad Transformers & Effect Monads

### State & StateT → Native Mutable State

```rust
// Before (0.17.0)
let computation = State::new(|s: i32| (s + 1, s * 2));
let (new_state, value) = computation.run_state(10);

// After (0.18.0)
fn step(s: &mut i32) -> i32 {
    let old = *s;
    *s += 1;
    old * 2
}

let mut state = 10;
let value = step(&mut state);
assert_eq!(state, 11);
assert_eq!(value, 20);
```

### Reader & ReaderT → Context Borrowing

```rust
// Before (0.17.0)
let computation = Reader::new(|env: &Config| env.timeout_ms);
let timeout = computation.run(&config);

// After (0.18.0)
fn get_timeout(env: &Config) -> u64 {
    env.timeout_ms
}
```

### IO → Native Execution

```rust
// Before (0.17.0)
let io_action = IO::new(|| read_file("config.json"));
let content = io_action.run();

// After (0.18.0)
let content = read_file("config.json");
```

### Writer → Mutable Buffer or Tracing

```rust
// Before (0.17.0)
let computation = Writer::new(42, vec!["computed answer"]);

// After (0.18.0)
let mut logs = Vec::new();
logs.push("computed answer");
let answer = 42;
```

---

## 2. Category Module

```rust
// Before (0.17.0)
use rustica::category::function_category::pipe;
let pipeline = pipe!(f, g, h);
let result = pipeline(input);

// After (0.18.0)
let result = h(g(f(input)));
// or with a closure:
let pipeline = |x| h(g(f(x)));
```

---

## 3. Monoidal Wrappers

| Wrapper | Replacement | Example |
| --- | --- | --- |
| `Sum(n)` | `n` + `Iterator::sum` | `numbers.iter().sum::<i32>()` |
| `Product(n)` | `n` + `Iterator::product` | `numbers.iter().product::<i32>()` |
| `Min(n)` | `std::cmp::min` | `a.min(b)` |
| `Max(n)` | `std::cmp::max` | `a.max(b)` |
| `First(opt)` | `Option::or` | `first.or(second)` |
| `Last(opt)` | `Option::or` reversed | `second.or(first)` |
| `Predicate(p)` | Closures `\|x\| p1(x) && p2(x)` | Direct boolean logic |
| `One` trait | Numeric literal `1` | `1_i32`, `1.0_f64` |

---

## 4. Error Handling

### ComposableError → ContextError

```rust
// Before (0.17.0)
use rustica::error::ComposableError;
let err = ComposableError::new("network failure")
    .with_context("requesting /api/v1/data".to_string());

// After (0.18.0)
use rustica::error::{ContextError, with_context_result};
use rustica::context;

let result: Result<(), _> = with_context_result(
    Err("network failure"),
    context!("requesting /api/v1/data")
);
```

### WithError & sequence_with_error → Standard Result

```rust
// Before (0.17.0)
use rustica::error::sequence_with_error;
let result = sequence_with_error(vec![Ok(1), Ok(2)]);

// After (0.18.0)
let result: Result<Vec<i32>, _> = vec![Ok(1), Ok(2)].into_iter().collect();
```

---

## 5. Free Monad

`Free::fold_map` has been removed because it imposed an unwanted dependency on `IO`. Use the stack-safe trampoline evaluator `Free::run` or `Free::try_run`:

```rust
// Before (0.17.0)
let io_prog = program.fold_map(|cmd| IO::new(move || interpret(cmd)));
let result = io_prog.run();

// After (0.18.0)
let result = program.run(|cmd| interpret(cmd));
```

Also, `Free::into_pure` has been removed in favor of `Free::to_pure` (following Rust API Guidelines C-CONV).

---

## 6. Optics (Lens & Prism)

`from_iso` constructors have been removed because the `Iso` trait was removed:

```rust
// Before (0.17.0)
let lens = Lens::from_iso(my_iso);

// After (0.18.0)
let lens = Lens::new(
    |s: &Source| s.to_focus(),
    |mut s: Source, focus| { s.set_focus(focus); s },
);
```

---

## 7. Choice

- Replace `choice.first()` with `choice.primary()`.
- Replace `choice.first_match(predicate)` with `choice.iter().find_map(predicate)`.
- Replace `choice.filter_values(predicate)` with `choice.filter(predicate)` (consumes `self`; clone the `Choice` first if it is reused).
- Monadic `bind` and `apply` are removed; `Choice` is purely a non-empty fallback/priority collection. Use `try_each` or `try_each_validated`.

---

## 8. Validated

- **Type Parameter Swap**: `Validated<E, A>` is now `Validated<T, E>` to match the standard library's `Result<T, E>` conventions:

  ```rust
  // Before (0.17.0)
  let v: Validated<&str, i32> = Validated::valid(42);

  // After (0.18.0)
  let v: Validated<i32, &str> = Validated::valid(42);
  ```

- **Inherent Mapping & Sequencing**:
  - `validated.bimap(f_val, g_err)` now takes the value transformer first and error transformer second, matching `Validated<T, E>`.
  - Inherent `validated.map(f)` replaces `map_valid(f)`.
  - Inherent `validated.map_err(g)` replaces `fmap_invalid(g)`.
  - Inherent sync `validated.and_then(f)` provides monadic chaining for dependent validation steps without requiring conversion to `Result`.
- Replace `validated.errors()` with `validated.error_slice()`.
- Replace `ErrorsIter` / `ErrorsIterMut` with standard slice iteration (`validated.iter_errors()`).
- `BinaryHKT` and `Bifunctor` traits are removed; call inherent `validated.bimap(...)`, `validated.map(...)`, and `validated.map_err(...)` directly.

---

## 9. Traits & Extension Traits

- The empty marker extension traits `FunctorExt`, `SemigroupExt`, `MonoidExt`, `PureExt`, and `FoldableExt` have been removed.
- `Foldable::fold_option` is now a default method directly on the `Foldable` trait:

  ```rust
  // Before (0.17.0)
  use rustica::traits::foldable::{Foldable, FoldableExt};
  let result = vec![1, 2, 3].fold_option(|&x| Some(TestSum(x)));

  // After (0.18.0)
  use rustica::traits::foldable::Foldable;
  let result = vec![1, 2, 3].fold_option(|&x| Some(TestSum(x)));
  ```

- `prelude::traits_ext` has been deleted; all core traits (`Functor`, `Applicative`, `Monad`, `Monoid`, `Semigroup`, `Foldable`, `Pure`, `HKT`) are available directly via `rustica::prelude::*` or `rustica::prelude::traits::*`.
- **Trait Bound Relaxation**:
  - Removed `E: Clone` bound from `Result<T, E>` implementations of `Pure`, `Functor`, `Applicative`, `Monad`, and `Foldable`.
  - Removed `T: Clone` bound from `Monoid for Vec<T>`.
- **Categorical Trait Deprecations (Removal in v0.19.0)**:
  - `Functor`, `Applicative`, `Monad`, `Pure`, `Foldable`, and `HKT` are deprecated in 0.18.0 and scheduled for deletion in 0.19.0.
  - Direct replacements:
    - `Functor::fmap` → Inherent `map` on `Validated`/`Choice`, or `Iterator::map`.
    - `Applicative::apply` / `lift2` → Inherent `Validated::zip_with`, `zip`, `zip_with3`, `lift2`, `lift3` (free of `Clone` bounds).
    - `Applicative::traverse` → Standard Rust `iter.collect::<Validated<Vec<T>, E>>()`.
    - `Monad::bind` / `join` → Inherent `and_then`, native `?`, or `Iterator::flat_map`.
    - `Foldable::fold_left` / `fold_right` → Standard `Iterator::fold` or `Iterator::rfold`.
    - `Pure::pure` → Concrete constructors (`Validated::valid`, `Choice::single`, `Some`, `Ok`).
  - `Semigroup` and `Monoid` are fully preserved as core algebraic abstractions.

---

## 10. PersistentVector Performance & Rebalancing

- **Buffer Pointer Sharing**: `head` and `tail` in `RRBTree<T>` are now wrapped in `Arc<SmallVec<[T; 32]>>`. `push_back(&self)` and `push_front(&self)` share opposite buffers via $O(1)$ pointer copy (`Arc::clone`) without duplicating up to 128 elements, guaranteeing true amortized $O(1)$ complexity.
- **In-Place Mutation**: Added `push_back_mut(&mut self, value)` and `push_front_mut(&mut self, value)` using `Arc::make_mut` to allow zero-allocation mutations when buffers are unshared.
- **Bagwell-Rompf RRB Rebalancing**: `concat` now rebalances internal and leaf nodes along boundary spines (`pack_children_balanced`, `pack_leaves_balanced`), enforcing a minimum occupancy of $\ge 16$ items per node for $N > 32$ and preventing unary tree degradation.

---

## 11. Choice Stack Optimization

- The internal storage for `Choice<T>::alternatives` has been migrated from `SmallVec<[T; 7]>` to `Vec<T>`. This reduces the default stack size of `Choice<T>` from over 56 bytes per instance down to 24 bytes, preventing stack overflows when nesting priority choices.

---

## 12. Prelude & Name Collisions

- `Command` has been removed from `rustica::prelude::*` to prevent shadowing `std::process::Command`. When defining commands for the operational monad, import it explicitly:

  ```rust
  use rustica::datatypes::operational::Command;
  ```

- `Handler`, `Program`, `TryHandler`, and `TryProgram` remain re-exported in the prelude.
- `Vec<T>` does not implement `Monad` to prevent `join` method resolution from shadowing standard slice `[T]::join`. Monadic operations on `Vec` should use standard iterator combinators (`flat_map`).

