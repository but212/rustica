# Operational Monad

The `operational` module provides operational monads ([`Program`] and [`TryProgram`])
where each [`Command`] statically declares its output type via [`Command::Output`].

## Type Safety Boundaries and Limitations

- **Handler interface**: The compiler enforces that [`Handler<C>::handle`] returns [`Command::Output`].
  Implementing a handler with the wrong return type is a compile error.
- **Trampoline evaluation**: Stack-safe execution requires intermediate type erasure via
  [`Box<dyn Any>`]. While the public API prevents mismatched types from being constructed,
  the execution engine relies on internal `.downcast::<T>().expect(...)` calls.
- **Handler coupling**: `Program<H, A>` fixes the handler type `H` at construction. Chaining commands
  requires `H` to implement `Handler<C>` for every command in the sequence.

## Architectural Role: `Program` vs `Free`

- Use [`Free`](crate::datatypes::free::Free) for an inspectable, cloneable DSL AST that can be
  transformed, analyzed across multiple passes, or evaluated across threads or backends. Backed by
  [`Arc`](alloc::sync::Arc), `Free` is first-class and maintained for concurrent or AST-centric architectures.
- Use [`Program`] / [`TryProgram`] for ownership-driven ([`Box`]), single-threaded operational execution
  pipelines. Without `Send + Sync` constraints, it seamlessly supports local state types such as
  [`Rc`](alloc::rc::Rc) and [`RefCell`](core::cell::RefCell) while checking command outputs against handler
  signatures at compile time.

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
