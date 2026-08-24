# Monoid Identity of `Min<T>` / `Max<T>` Wrappers

Known limitation of the numeric monoid wrappers, verified by the
`test_max_min_identity_law_boundary` regression test in
`tests/datatypes/test_wrapper.rs`.

## The issue

`Monoid::empty()` for both wrappers is defined as `T::default()`:

- `Max::<T>::empty() == Max(T::default())`
- `Min::<T>::empty() == Min(T::default())`

The monoid identity laws (`x ⊕ empty() == x == empty() ⊕ x`) hold only when
`T::default()` is the true extremum of `T`. For standard numeric types this
is rarely the case, because `T::default()` is zero:

| Wrapper | Required identity | `T::default()` | Lawful with `default()`? |
| --------- | ------------------- | ---------------- | -------------------------- |
| `Max<u32>` | minimum of `T` | 0 (= `u32::MIN`) | Yes |
| `Max<i32>` | minimum of `T` | 0 (≠ `i32::MIN`) | No |
| `Min<u32>` | maximum of `T` | 0 (≠ `u32::MAX`) | No |
| `Min<i32>` | maximum of `T` | 0 (≠ `i32::MAX`) | No |

## Counterexamples

```rust
use rustica::datatypes::wrapper::{max::Max, min::Min};
use rustica::prelude::*;

// Violates right identity: combining a negative value with the default
// identity yields Max(0), not Max(-1).
assert_eq!(Max(-1).combine(&Max::<i32>::empty()), Max(0));

// Min requires the maximum value as its identity; default() is the minimum,
// so this fails for unsigned types too.
assert_eq!(Min(1).combine(&Min::<i32>::empty()), Min(0));
```

## Workaround

Supply the true extremum explicitly instead of relying on `empty()`:

```rust
use rustica::datatypes::wrapper::{max::Max, min::Min};
use rustica::traits::semigroup::Semigroup;

let max_identity = Max(i32::MIN);
let min_identity = Min(i32::MAX);

assert_eq!(Max(-1).combine(&max_identity), Max(-1));
assert_eq!(Min(1).combine(&min_identity), Min(1));
```

## Scope

`Semigroup` (associativity) and all other wrapper operations are unaffected.
Only `Monoid::empty()` for `Min<T>`/`Max<T>` over types whose `Default`
differs from their extremum is affected. A lawful redesign (for example,
wrapping the inner value in an option-like type so that "empty" is
representable) would be a breaking change and is tracked separately.
