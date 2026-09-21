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
| `traits::Bifunctor`, `BinaryHKT` | Inherent `Validated::bimap`, `map_valid`, `map_err` |
| `traits::Iso` | Standard `From` / `Into` conversions |
| `traits::MonadError` | `Result::or_else`, `?` operator |
| `traits::One` | Numeric literals (`1`) or `Iterator::product` |
| `Free::fold_map` | `Free::run` or `Free::try_run` with trampoline evaluation |
| `Free::into_pure` | `Free::to_pure` |
| `Lens::from_iso`, `Prism::from_iso` | `Lens::new` or `Prism::new` directly with closures |

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

- Replace `validated.errors()` with `validated.error_slice()`.
- Replace `ErrorsIter` / `ErrorsIterMut` with standard slice iteration (`validated.iter_errors()`).
- `BinaryHKT` and `Bifunctor` traits are removed; call inherent `validated.bimap(...)`, `validated.map_valid(...)`, and `validated.map_err(...)` directly.

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
