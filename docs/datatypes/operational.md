# Operational Monad

Operational monads ([`Program`] and [`TryProgram`]) where each [`Command`] statically declares its output type via [`Command::Output`].

## Type Safety Boundaries and Limitations

- **Handler interface**: Compiler enforces that [`Handler<C>::handle`] returns [`Command::Output`].
- **Trampoline evaluation**: Stack-safe execution uses intermediate type erasure via [`Box<dyn Any>`]. Internal `.downcast::<T>().expect(...)` calls rely on public API type invariance.
- **Handler coupling**: `Program<H, A>` statically fixes handler `H` at construction; `H` must implement `Handler<C>` for every command in the sequence.

## Architectural Role: `Program` vs `Free`

- **[`Program`] / [`TryProgram`]**: Ownership-driven ([`Box`]), single-threaded execution pipelines. Supports local state types ([`Rc`](alloc::rc::Rc), [`RefCell`](core::cell::RefCell)) without `Send + Sync` bounds, checking command outputs against handler signatures at compile time.
- **[`Free`](crate::datatypes::free::Free)**: Inspectable, cloneable DSL AST backed by [`Arc`](alloc::sync::Arc) for concurrent or multi-pass architectures.

## Example

```rust
use rustica::datatypes::operational::{Command, Handler, Program};

struct Add(i32);
impl Command for Add {
    type Output = ();
}

struct Multiply(i32);
impl Command for Multiply {
    type Output = ();
}

struct Get;
impl Command for Get {
    type Output = i32;
}

let program = Add(5).suspend()
    .then(Multiply(3).suspend())
    .then(Get.suspend());

struct Calculator {
    current: i32,
}

impl Handler<Add> for Calculator {
    fn handle(&mut self, cmd: Add) {
        self.current += cmd.0;
    }
}

impl Handler<Multiply> for Calculator {
    fn handle(&mut self, cmd: Multiply) {
        self.current *= cmd.0;
    }
}

impl Handler<Get> for Calculator {
    fn handle(&mut self, _cmd: Get) -> i32 {
        self.current
    }
}

let mut calc = Calculator { current: 0 };
let result = program.run(&mut calc);
assert_eq!(result, 15);
```
