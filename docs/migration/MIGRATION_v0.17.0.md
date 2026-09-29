# Rustica 0.17.0 Migration Guide

This guide describes the deprecations, standard library replacements, and migration paths introduced in Rustica 0.17.0.

## Summary of Deprecations

| Deprecated API | Target Version | Recommended Replacement | Rationale |
| --- | --- | --- | --- |
| `Id<T>` | 0.18.0 | Plain Rust value / expression, `std::convert::identity` | Redundant monadic wrapper in idiomatic Rust. |
| `First<T>` | 0.18.0 | `Option::or`, `Option::or_else` | Direct standard library `Option` combinator. |
| `Last<T>` | 0.18.0 | `Option::or`, `Option::or_else` (swapped operands) | Direct standard library `Option` combinator. |
| `Min<T>` | 0.18.0 | `std::cmp::min`, `Iterator::min` | Standard comparison function and iterator reductions. |
| `Max<T>` | 0.18.0 | `std::cmp::max`, `Iterator::max` | Standard comparison function and iterator reductions. |
| `Sum<T>` | 0.18.0 | `std::iter::Sum`, `+`, `Iterator::sum` | Standard library arithmetic and iterator summation. |
| `Product<T>` | 0.18.0 | `std::iter::Product`, `*`, `Iterator::product` | Standard library arithmetic and iterator product. |
| `Predicate<A>` | 0.18.0 | Standard closures `\|x\| ...`, `\|\|`, `&&`, `!` | `Arc<dyn Fn>` dynamic dispatch overhead replaced by zero-cost closures. |
| `One` trait | 0.18.0 | Numeric literals (`1`, `1.0`), `Iterator::product` | Multiplicative identity provided natively by standard numeric types. |
| `Choice::first_match` | 0.18.0 | `choice.iter().find_map(f)` | Standard iterator short-circuiting combinator. |
| `FoldableExt::to_vec` | 0.18.0 | `Iterator::collect::<Vec<_>>()` | Idiomatic collection conversion. |
| `FoldableExt::sum_values` | 0.18.0 | `Iterator::sum()` | Direct standard iterator sum. |
| `FoldableExt::product_values` | 0.18.0 | `Iterator::product()` | Direct standard iterator product. |
| `FoldableExt::maximum` | 0.18.0 | `Iterator::max()` | Zero-copy standard iterator maximum. |
| `FoldableExt::minimum` | 0.18.0 | `Iterator::min()` | Zero-copy standard iterator minimum. |
| `FoldableExt::reduce` | 0.18.0 | `Iterator::reduce()` | Standard iterator reduction. |
| `State<S, A>`, `StateInner` | 0.18.0 | `&mut S`, pure functions `Fn(S) -> (S, A)` | Standard Rust borrow checker and mutable references. |
| `Reader<E, A>` | 0.18.0 | `&Context`, closures | Standard Rust reference borrowing and dependency injection. |
| `Cont<R, A>`, `ContFn2` | 0.18.0 | `async / await`, standard closures, early `return` | Standard Rust language-level control flow. |
| `StateT<S, M, A>` | 0.18.0 | `&mut S`, pure transition functions | Transformer overhead eliminated in favor of native Rust patterns. |
| `ReaderT<E, M, A>` | 0.18.0 | `&Context`, dependency injection | Replaced by standard Rust borrowing. |
| `ContT<R, M, A>`, `ContTFn` | 0.18.0 | `async / await`, coroutines, closures | Native language features provide better ergonomics and zero overhead. |
| `MonadTransformer`, `lift` | 0.18.0 | Direct composition | Entire transformer subsystem scheduled for removal. |
| `FunctionCategory`, `FunctionMorphism`, `PairMorphism` | 0.18.0 | Standard closures `\|x\| ...`, `map`, iterators | `Arc<dyn Fn>` dynamic dispatch overhead replaced by zero-cost closures. |
| `IO<A>`, `IOMorphism`, `IOError` | 0.18.0 | Direct synchronous execution, closures, `async/await` | Impure Rust needs no lazy IO monadic wrapper. |
| `Writer<W, A>` | 0.18.0 | `&mut Buffer`, `tracing`/`log`, tuple `(T, Log)` | $O(N^2)$ immutable buffer reallocations replaced by $O(1)$ amortized mutation. |
| `MonadError<E>` trait | 0.18.0 | `Result::or_else`, `Option::or_else`, `?`, `match` | Duplicate of native Result/Option methods and language-level operators. |
| `Alternative` trait | 0.18.0 | `Option::or`, `Vec::extend`, `bool::then_some` | Duplicate of standard Option, Vec, and bool primitives. |
| `ErrorsIter<'a, E>`, `ErrorsIterMut<'a, E>` | 0.18.0 | `std::slice::Iter<'a, E>`, `std::slice::IterMut<'a, E>` | Custom enum with empty variants replaced by standard slice iterators. |
| `Free::into_pure` | 0.18.0 | `Free::to_pure` | Aligns receiver semantics (`&self` with cloned inner) with C-CONV. |

---

## Migration Details & Examples

### 1. `First<T>` and `Last<T>` -> `Option::or`

`First` and `Last` were Semigroup newtype wrappers around `Option<T>`.

**Before (0.16.0):**

```rust
use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::traits::semigroup::Semigroup;

let first = First(Some(1)).combine(First(Some(2))).into_inner(); // Some(1)
let last = Last(Some(1)).combine(Last(Some(2))).into_inner();   // Some(2)
```

**After (0.17.0+):**

```rust
let a = Some(1);
let b = Some(2);

let first = a.or(b); // Some(1)
let last = b.or(a);  // Some(2)
```

---

### 2. `Min<T>` and `Max<T>` -> `std::cmp::min` / `max` / `Iterator::min` / `max`

**Before (0.16.0):**

```rust
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::max::Max;
use rustica::traits::semigroup::Semigroup;

let smallest = Min(10).combine(Min(5)).into_inner();
let largest = Max(10).combine(Max(5)).into_inner();
```

**After (0.17.0+):**

```rust
let smallest = std::cmp::min(10, 5);
let largest = std::cmp::max(10, 5);

// For collections:
let numbers = [10, 5, 20];
let smallest = numbers.iter().min().copied();
let largest = numbers.iter().max().copied();
```

---

### 3. `Sum<T>` and `Product<T>` -> `std::iter::Sum` / `Product`

**Before (0.16.0):**

```rust
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::product::Product;
use rustica::traits::semigroup::Semigroup;

let total = Sum(10).combine(Sum(5)).into_inner();
let prod = Product(10).combine(Product(5)).into_inner();
```

**After (0.17.0+):**

```rust
let total = 10 + 5;
let prod = 10 * 5;

// For collections:
let numbers = [1, 2, 3, 4];
let total: i32 = numbers.iter().sum();
let prod: i32 = numbers.iter().product();
```

---

### 4. `Id<T>` -> Plain Values & Closures

**Before (0.16.0):**

```rust
use rustica::datatypes::id::Id;
use rustica::traits::functor::Functor;

let result = Id::new(42).fmap(|x| x * 2).into_inner();
```

**After (0.17.0+):**

```rust
let x = 42;
let result = x * 2; // or (|x| x * 2)(42) / std::convert::identity
```

---

### 5. `Choice::first_match` -> `Iterator::find_map`

**Before (0.16.0):**

```rust
let choice = Choice::new(10, [20, 30]);
let res = choice.first_match(|&x| if x > 15 { Some(x * 2) } else { None });
```

**After (0.17.0+):**

```rust
let choice = Choice::new(10, [20, 30]);
let res = choice.iter().find_map(|&x| if x > 15 { Some(x * 2) } else { None });
```

---

### 6. `FoldableExt` Redundant Reductions -> `Iterator`

**Before (0.16.0):**

```rust
use rustica::traits::foldable::FoldableExt;

let v = vec![1, 2, 3];
let sum = v.sum_values();
let prod = v.product_values();
let max = v.maximum();
let min = v.minimum();
let reduced = v.reduce(|a, b| a + b);
let cloned = v.to_vec();
```

**After (0.17.0+):**

```rust
let v = vec![1, 2, 3];
let sum: i32 = v.iter().sum();
let prod: i32 = v.iter().product();
let max = v.iter().max().copied();
let min = v.iter().min().copied();
let reduced = v.iter().copied().reduce(|a, b| a + b);
let cloned = v.clone();
```

---

### 7. `State<S, A>` & `StateT<S, M, A>` -> Mutable References (`&mut S`) or Transition Functions

Mutable references (`&mut S`) provide zero-cost, statically checked state tracking without boxed closures.

**Before (0.16.0):**

```rust
use rustica::datatypes::state::State;

let counter = State::new(|count: i32| (count + 1, count));
let (new_count, result) = counter.run_state(0);
```

**After (0.17.0+):**

```rust
// Idiomatic pattern 1: Mutable variable / reference
let mut count = 0;
let result = {
    let old = count;
    count += 1;
    old
};

// Idiomatic pattern 2: Pure state function
fn step(count: i32) -> (i32, i32) {
    (count + 1, count)
}
let (new_count, result) = step(0);
```

---

### 8. `Reader<E, A>` & `ReaderT<E, M, A>` -> Reference Borrowing (`&Context`)

Borrowing shared context (`&Context` / `&Config`) is zero-cost and avoids closure-wrapping monads.

**Before (0.16.0):**

```rust
use rustica::datatypes::reader::Reader;

struct Config { port: u16 }
let reader: Reader<Config, String> = Reader::new(|c: Config| format!("localhost:{}", c.port));
let addr = reader.run_reader(Config { port: 8080 });
```

**After (0.17.0+):**

```rust
struct Config { port: u16 }

fn get_address(config: &Config) -> String {
    format!("localhost:{}", config.port)
}

let cfg = Config { port: 8080 };
let addr = get_address(&cfg);
```

---

### 9. `Cont<R, A>` & `ContT<R, M, A>` -> Native Control Flow / `async` / Callbacks

Language-level control flow (`return`, `?`), closures, and `async`/`await` provide coroutines and early exits without `Arc<dyn Fn...>` allocation.

**Before (0.16.0):**

```rust
use rustica::datatypes::cont::Cont;

let cont: Cont<i32, i32> = Cont::return_cont(42);
let res = cont.run(|x| x * 2);
```

**After (0.17.0+):**

```rust
// Idiomatic callback / closure
fn with_computation<F: FnOnce(i32) -> i32>(f: F) -> i32 {
    f(42)
}
let res = with_computation(|x| x * 2);
```

---

### 10. `transformers` Subsystem (`MonadTransformer`, `lift`)

Deprecated in its entirety. Replace transformer stacks (`ReaderT<StateT<...>>`) with standard types (`Option`, `Result`) and native combinators (`?`, `and_then`, `map`).

---

### 11. `FunctionCategory` -> Standard Closures & Iterators

Standard closures are monomorphized and zero-cost, avoiding `Arc<dyn Fn...>` heap allocation and dynamic dispatch.

**Before (0.16.0):**

```rust
use rustica::category::function_category::FunctionCategory;

let double = FunctionCategory::arrow(|x: i32| x * 2);
let add_one = FunctionCategory::arrow(|x: i32| x + 1);
let composed = FunctionCategory::compose_morphisms(&double, &add_one);
assert_eq!(composed(5), 12);
```

**After (0.17.0+):**

```rust
// Idiomatic Rust: direct closure composition
let double = |x: i32| x * 2;
let add_one = |x: i32| x + 1;
let result = double(add_one(5));
assert_eq!(result, 12);

// Or via iterator pipeline
let result = Some(5).map(|x| x + 1).map(|x| x * 2);
assert_eq!(result, Some(12));
```

---

### 12. `IO<A>` -> Eager Functions or Closures

Direct side-effect execution requires no monadic wrapper in Rust. For deferred evaluation, zero-cost closures (`|| ...`) or `async`/`await` offer simpler ergonomics and higher performance.

**Before (0.16.0):**

```rust
use rustica::datatypes::io::IO;

let program = IO::pure(21)
    .fmap(|x| x * 2)
    .bind(|x| IO::pure(x + 1));
let result = program.run();
```

**After (0.17.0+):**

```rust
// Idiomatic eager execution
let result = {
    let x = 21 * 2;
    x + 1
};

// Idiomatic deferred (lazy) execution
let compute = || (21 * 2) + 1;
let result = compute();
```

---

### 13. `Writer<W, A>` -> Mutable Buffer or Tuples

Immutable log combination incurs $O(N^2)$ reallocation. Borrowing `&mut Buffer` provides $O(1)$ amortized appends with zero copies.

**Before (0.16.0):**

```rust
use rustica::datatypes::writer::Writer;

let w = Writer::new("step1 ".to_string(), 10)
    .bind(|x| Writer::new("step2".to_string(), x * 2));
let (log, val) = w.run();
```

**After (0.17.0+):**

```rust
// Idiomatic pattern 1: Mutable buffer (Zero-copy, O(1))
let mut log = String::new();
log.push_str("step1 ");
let val = 10 * 2;
log.push_str("step2");

// Idiomatic pattern 2: Explicit tuple (T, Log)
fn step1() -> (i32, &'static str) { (10, "step1 ") }
fn step2(x: i32) -> (i32, &'static str) { (x * 2, "step2") }
```

---

### 14. `MonadError<E>` -> `Result::or_else` / `Option::or_else` / `?` / `match`

`MonadError::throw` and `catch` duplicate standard Rust error handling.

**Before (0.16.0):**

```rust
use rustica::traits::monad_error::MonadError;

let res: Result<i32, &str> = Result::throw("fail");
let recovered = res.catch(|_| Ok(0));
```

**After (0.17.0+):**

```rust
let res: Result<i32, &str> = Err("fail");
let recovered = res.or_else(|_| Ok(0));
```

---

### 15. `Alternative` -> `Option::or` / `Vec::extend` / `bool::then_some`

`Alternative::alt`, `empty_alt`, and `guard` duplicate standard library operations that are explicit and zero-cost.

**Before (0.16.0):**

```rust
use rustica::traits::alternative::Alternative;

let chosen = Some(1).alt(Some(2));
let guard = Option::<i32>::guard(true);
```

**After (0.17.0+):**

```rust
let chosen = Some(1).or(Some(2));
let guard = true.then_some(());
```

---

### 16. `ErrorsIter` / `ErrorsIterMut` -> `std::slice::Iter` / `IterMut`

`Validated::iter_errors()` and `iter_errors_mut()` now directly return standard slice iterators.

**Before (0.16.0):**

```rust
use rustica::datatypes::validated::iter::ErrorsIter;

match validated.iter_errors() {
    ErrorsIter::Empty => {},
    ErrorsIter::Multi(mut it) => {
        let first = it.next();
    },
}
```

**After (0.17.0+):**

```rust
// Direct standard iterator usage
for err in validated.iter_errors() {
    println!("{err}");
}

// Or borrow slice directly
for err in validated.error_slice() {
    println!("{err}");
}
```

---

### 17. `Predicate<A>` -> Standard Closures & Boolean Operators

`Predicate<A>` wraps `Arc<dyn Fn(&A) -> bool + Send + Sync>` and allocates new `Arc` closures on combination (`union`, `intersection`, `diff`, `negate`). Replace with zero-cost standard Rust closures and language-level boolean operators (`||`, `&&`, `!`).

**Before (0.16.0):**

```rust
use rustica::datatypes::wrapper::predicate::Predicate;

let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
let is_positive = Predicate::new(|x: &i32| *x > 0);

let even_or_positive = is_even.union(&is_positive);
let even_and_positive = is_even.intersection(&is_positive);
let odd = is_even.negate();

assert!(even_or_positive.contains(&2));
assert!(even_and_positive.contains(&2));
assert!(odd.contains(&3));
```

**After (0.17.0+):**

```rust
let is_even = |x: &i32| *x % 2 == 0;
let is_positive = |x: &i32| *x > 0;

let even_or_positive = |x: &i32| is_even(x) || is_positive(x);
let even_and_positive = |x: &i32| is_even(x) && is_positive(x);
let odd = |x: &i32| !is_even(x);

assert!(even_or_positive(&2));
assert!(even_and_positive(&2));
assert!(odd(&3));
```
