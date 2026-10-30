# Rustica 0.22.0 Migration Guide

Breaking changes in Rustica 0.22.0. Every removed item was deprecated in 0.21.0 and has a replacement, except `datatypes::validated::core` and the `Program` tuple struct, which were changed without deprecation (see below). Only `Prism::set_with` and `Prism::modify_with` change behavior: their replacements do not preserve non-focus fields (see below).

**API Stability Policy (0.22.0+):** Rustica 0.22.0 completes the surface reduction and architectural consolidation started in 0.14.0. Starting with 0.22.0, no further sweeping API removals or big-bang breaking releases are planned.

---

## Quick Reference

| Item | Status | Replacement |
| --- | --- | --- |
| `Validated::lift2` | Removed | `v1.zip_with(v2, f)` |
| `Validated::lift3` | Removed | `v1.zip_with3(v2, v3, f)` |
| `Free::lift2` | Removed | `fa.zip_with(fb, f)` |
| `operational::suspend` | Removed | `Command::suspend` or `Program::suspend` |
| `operational::try_suspend` | Removed | `Command::try_suspend` or `TryProgram::suspend` |
| `ContextError::context_iter` | Removed | `err.contexts().iter()` |
| `error::context_fn` | Removed | `with_context(e, c)` or `ContextError::new(e).with_context(c)` |
| `prelude::error::context_fn` | Removed | `prelude::error::with_context` |
| `Validated::collect` | Removed | `iter.into_iter().collect::<Validated<C, E>>()` |
| `Validated::sequence` | Removed | `values.into_iter().collect::<Validated<Vec<_>, _>>().map(f)` |
| `Prism::set_with` | Removed | `set_always` (or `set`) |
| `Prism::modify_with` | Removed | `modify_always` (or `modify`) |
| `Choice::flatten` | Removed | `try_flatten().ok()`, or `try_flatten()` to keep `ChoiceError` |
| `datatypes::error` module | Removed | `rustica::datatypes::{ChoiceError, FreeError}` or `rustica::prelude::*` |
| `datatypes::validated::core` module | Removed (private) | `rustica::datatypes::validated::{Validated, NonEmptyErrors}` |
| `Program(p)` / `program.0` | Removed (tuple struct) | `p` directly; `Program<H, A>` is `TryProgram<H, A, Infallible>` |

## Combinator Functions Removed

Deprecated in 0.21.0 in favor of method syntax:

```rust,ignore
// Before (0.21.0)
let sum = Validated::lift2(|a, b| a + b, v1, v2);
let total = Validated::lift3(|a, b, c| a + b + c, v1, v2, v3);
let free_sum = Free::lift2(|a, b| a + b, fa, fb);

// After (0.22.0)
let sum = v1.zip_with(v2, |a, b| a + b);
let total = v1.zip_with3(v2, v3, |a, b, c| a + b + c);
let free_sum = fa.zip_with(fb, |a, b| a + b);
```

## Operational Free Functions Removed

Deprecated in 0.21.0 in favor of `Command` extension methods and program constructors:

```rust,ignore
// Before (0.21.0)
let prog: Program<H, ()> = operational::suspend(Add(10));
let try_prog: TryProgram<H, (), E> = operational::try_suspend(Add(20));

// After (0.22.0)
let prog: Program<H, ()> = Add(10).suspend();
let try_prog: TryProgram<H, (), E> = Add(20).try_suspend();

// Equivalent
let prog: Program<H, ()> = Program::suspend(Add(10));
let try_prog: TryProgram<H, (), E> = TryProgram::suspend(Add(20));
```

## `ContextError` Accessors and Helpers Removed

`ContextError::context_iter` iterates the same newest-first slice as `contexts()`:

```rust,ignore
// Before (0.21.0)
let messages: Vec<&str> = err.context_iter().map(String::as_str).collect();

// After (0.22.0)
let messages: Vec<&str> = err.contexts().iter().map(String::as_str).collect();
```

`error::context_fn` returned a closure attaching fixed context. Build the closure directly:

```rust,ignore
// Before (0.21.0)
use rustica::error::context_fn;
let attach = context_fn("step failed");
let err = attach("io timeout");

// After (0.22.0)
use rustica::error::with_context;
let err = with_context("io timeout", "step failed");

// Or, when the closure is needed:
let attach = |e| with_context(e, "step failed");
```

The `context_fn` re-export in `rustica::prelude::error` was removed with it.

## `Validated::collect` and `Validated::sequence` Removed

Deprecated in 0.21.0 in favor of `FromIterator`; behavior is unchanged:

```rust,ignore
// Before (0.21.0)
let collected: Validated<Vec<i32>, &str> = Validated::collect(values);
let total = Validated::sequence(values, |vals| vals.len());

// After (0.22.0)
let collected: Validated<Vec<i32>, &str> = values.into_iter().collect();
let total = values.into_iter().collect::<Validated<Vec<_>, _>>().map(|vals| vals.len());
```

## `Prism::set_with` and `Prism::modify_with` Removed

These took a closure to rebuild the source while preserving non-focus data. Focus the whole variant payload and use the `*_always` variants (or `set` / `modify`) with the prism's review function:

```rust,ignore
// Before (0.21.0)
let updated = prism.set_with(item, |item, id| rebuild(item, id), 99);
let modified = prism.modify_with(item, |item, id| rebuild(item, id), |id| id + 5);

// After (0.22.0)
let updated = prism.set_always(item, 99);
let modified = prism.modify_always(item, |id| id + 5);
```

Non-focus fields are not preserved. Review rebuilds the variant from the focused value, resetting any field outside the focus. To keep such fields, focus a type that contains them, or update the value with a `match` directly.

## `Choice::flatten` Removed

`Choice::flatten` returned `None` on empty input. `try_flatten` returns the same information as a `Result`:

```rust,ignore
// Before (0.21.0)
let flat: Option<Choice<I>> = nested.flatten();

// After (0.22.0)
let flat: Option<Choice<I>> = nested.try_flatten().ok();

// Or keep the error:
let flat: Result<Choice<I>, ChoiceError> = nested.try_flatten();
```

## `datatypes::error` Module Removed

Deprecated in 0.21.0. Import from the canonical path:

```rust,ignore
// Before (0.21.0)
use rustica::datatypes::error::{ChoiceError, FreeError};

// After (0.22.0)
use rustica::datatypes::{ChoiceError, FreeError};
// or
use rustica::prelude::*;
```

## `validated::core` Module Path Removed

The `rustica::datatypes::validated::core` module was public in 0.21.0 and is now private. It was removed without a deprecation period: a deprecated public module still shadows the `core` crate under `use rustica::datatypes::validated::*`, so the glob import broke `core::…` paths in downstream code. Import from the parent module:

```rust,ignore
// Before (0.21.0)
use rustica::datatypes::validated::core::{NonEmptyErrors, Validated};

// After (0.22.0)
use rustica::datatypes::validated::{NonEmptyErrors, Validated};
```

## `Program` Newtype Replaced by Alias

`Program<H, A>` was a tuple struct around `TryProgram<H, A, Infallible>` in 0.21.0. It became a type alias in 0.22.0 without a deprecation period, so the `Program(..)` constructor and the `.0` field no longer exist. The constructors, combinators, `run`, and `is_*` predicates are unchanged; they come from `TryProgram`, and `Debug` output is the same:

```rust,ignore
// Before (0.21.0)
let prog: Program<H, ()> = Program(try_prog);
let inner: TryProgram<H, (), Infallible> = prog.0;

// After (0.22.0)
let prog: Program<H, ()> = try_prog;
let inner: TryProgram<H, (), Infallible> = prog;
```

Because `Program` is an alias, `try_run` (which returns `Result<A, Infallible>`) is also available on it.
