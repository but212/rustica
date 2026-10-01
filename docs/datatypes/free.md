# Free Monad

`Free<F, A>` represents a computation tree of commands `F`, separating program
definition from execution.

## Execution and Stack Safety

- **Evaluation**: Evaluated via [`run`](Free::run) or [`try_run`](Free::try_run). An internal stack unwinds left-associated chains (`a.then(b).then(c)`), maintaining $O(1)$ call stack frames.
- **Error handling**: [`try_run`](Free::try_run) returns [`FreeError`] on interpreter error or downcast mismatch without panicking.
- **Drop and Debug**: Traverses chains iteratively to prevent stack overflow on deep programs.
- **Reuse**: Backed by `Arc`, enabling AST cloning and repeated execution.

## Architectural Role: `Free` vs `Program`

- **`Free<F, A>` (DSL AST Engine)**: Cloneable computation trees backed by `Arc` for multi-pass interpretation. Node shapes are inspectable via [`is_pure`](Free::is_pure), [`is_suspend`](Free::is_suspend), [`is_bind`](Free::is_bind), and [`is_then`](Free::is_then); inspect effect commands via [`as_suspend`](Free::as_suspend), pure values via [`as_pure`](Free::as_pure), and static sequencing trees via [`as_then`](Free::as_then). Dynamic continuations (`Bind`) remain opaque. Stack safety applies to `Bind` and `Then` spines.
- **[`Program<H, A>`](crate::datatypes::operational::Program) (Operational Pipeline)**: Statically couples commands to handler `H` at compile time, eliminating runtime downcasts in handler interfaces via trampoline evaluation.

## Example

```rust
use rustica::datatypes::free::{any_value, AnyValue, Free};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum CalcOp {
    Add(i32),
    Multiply(i32),
    Get,
}

impl CalcOp {
    fn add(n: i32) -> Free<Self, ()> {
        Free::suspend(Self::Add(n))
    }

    fn multiply(n: i32) -> Free<Self, ()> {
        Free::suspend(Self::Multiply(n))
    }

    fn get() -> Free<Self, i32> {
        Free::suspend(Self::Get)
    }
}

let program = CalcOp::add(5)
    .then(CalcOp::multiply(3))
    .then(CalcOp::get());

let mut current = 0;
let result: i32 = program.run(|op| match op {
    CalcOp::Add(n) => {
        current += n;
        any_value(())
    }
    CalcOp::Multiply(n) => {
        current *= n;
        any_value(())
    }
    CalcOp::Get => any_value(current),
});

assert_eq!(result, 15);

// The same program can be evaluated again with different state
let mut current2 = 10;
let result2: i32 = program.run(|op| match op {
    CalcOp::Add(n) => {
        current2 += n;
        any_value(())
    }
    CalcOp::Multiply(n) => {
        current2 *= n;
        any_value(())
    }
    CalcOp::Get => any_value(current2),
});
assert_eq!(result2, 45); // (10 + 5) * 3 = 45
```
