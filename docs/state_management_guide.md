# Practical Guide: Functional State Management with the State Monad

Managing state is a central challenge in software development. While Rust's ownership model provides strong guarantees against data races, managing complex, evolving state can still lead to complicated code. The **State monad** offers a classic functional programming pattern for handling state in a pure, composable, and predictable way.

This guide will show you how to use Rustica's `State` monad to build stateful computations without relying on mutable variables.

## 1. What is the `State` Monad?

At its core, `State<S, A>` represents a computation that takes an initial state of type `S` and produces a result of type `A` along with a new state of type `S`. It wraps a function with the signature `S -> (A, S)`.

This simple wrapper allows us to chain and compose stateful operations together, where each operation implicitly receives the state from the previous one and passes its new state to the next.

This is useful for:

- Building parsers that consume input.
- Managing game state or simulations.
- Implementing algorithms that require intermediate state.
- Any scenario where you want to model a sequence of state changes purely.

## 2. Creating and Running a `State` Computation

You can create a `State` computation directly with `State::new`, which takes a function that defines the state transition.

```rust
use rustica::datatypes::state::State;

// A computation that returns the current state as the value,
// and increments the state by 1.
let counter: State<i32, i32> = State::new(|s: i32| (s, s + 1));
```

This computation doesn't _do_ anything on its own. It's a description of a state change. To execute it, you use one of the `run` methods with an initial state:

- `run_state(initial_state)`: Returns both the final result and the final state.
- `eval_state(initial_state)`: Returns only the final result.
- `exec_state(initial_state)`: Returns only the final state.

```rust
let initial_state = 10;

// Run and get both value and new state
let (value, new_state) = counter.run_state(initial_state);
// value is 10, new_state is 11

// Run and get only the value
let value_only = counter.eval_state(initial_state);
// value_only is 10

// Run and get only the new state
let state_only = counter.exec_state(initial_state);
// state_only is 11
```

## 3. Core State Operations

While you can define any state transition with `State::new`, Rustica provides three fundamental helpers for common operations.

- `get()`: Returns the current state as the value, without changing the state.
- `put(new_state)`: Replaces the current state with a new one.
- `modify(f)`: Applies a function to the current state to compute a new state.

```rust
use rustica::datatypes::state::{State, get, modify, put};

// get(): Read the state
let read_state: State<String, String> = get();
let (value, state) = read_state.run_state("hello".to_string());
// value is "hello", state is "hello"

// put(): Overwrite the state
let write_state: State<&str, ()> = put("world");
let (value, state) = write_state.run_state("hello");
// value is (), state is "world"

// modify(): Update the state
let update_state: State<i32, ()> = modify(|s| s * 2);
let (value, state) = update_state.run_state(10);
// value is (), state is 20
```

These three simple functions are the building blocks for all other stateful logic.

## 4. Composing Operations with `bind`

The true power of the `State` monad comes from `bind`, which allows you to sequence operations. It takes the result of one computation and uses it to decide what computation to run next.

Let's create a computation that:

1. Gets the current state (an integer).
2. Adds that value back to the state.
3. Returns the new state as the result.

```rust
use rustica::datatypes::state::{get, modify};

let computation = get::<i32>()
    .bind(|current_value| {
        // `current_value` is the result of `get()`
        // Now we can use it to create the next operation
        modify(move |s| s + current_value)
    })
    .bind(|_| {
        // The result of `modify` is `()`, so we ignore it
        // and get the final state to return as the result.
        get()
    });

// Initial state: 10
// 1. get() -> value is 10, state is 10
// 2. modify(|s| s + 10) -> value is (), new state is 20
// 3. get() -> value is 20, state is 20
let (final_value, final_state) = computation.run_state(10);
// final_value is 20, final_state is 20
```

With `bind`, you can build complex, sequential stateful logic in a clean, declarative way.

## 5. Practical Example: A Functional Stack

Let's implement a stack data structure. The state will be a `Vec<i32>`.

```rust
use rustica::datatypes::state::{State, modify};

// Pushes a value onto the stack.
fn push(value: i32) -> State<Vec<i32>, ()> {
    modify(move |mut stack: Vec<i32>| {
        stack.push(value);
        stack
    })
}

// Pops a value from the stack, returning it as the result.
fn pop() -> State<Vec<i32>, Option<i32>> {
    State::<Vec<i32>, Option<i32>>::new(|mut stack: Vec<i32>| {
        let result = stack.pop();
        (result, stack)
    })
}

let stack_program = push(10)
    .bind(|_| push(20))
    .bind(|_| pop())
    .bind(|popped_value1| {
        // The result of this bind is another State computation
        pop().fmap(move |popped_value2| (popped_value1, popped_value2))
    });

let initial_stack = vec![];
let (final_result, final_stack) = stack_program.run_state(initial_stack);
// final_result is (Some(20), Some(10)), final_stack is []
```

This example shows how to build up a sequence of operations that manipulate a stack, all without a single mutable variable in our `main` function's scope.

## Conclusion

The `State` monad is a powerful tool for writing pure, functional, and stateful code. It allows you to turn complex, imperative sequences of state mutations into a clear, declarative workflow. By separating the description of the state changes from their execution, you can build more predictable, testable, and maintainable systems.
