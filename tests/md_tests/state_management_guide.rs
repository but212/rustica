#[test]
fn creating_and_running_a_state_computation() {
    use rustica::datatypes::state::State;

    let counter: State<i32, i32> = State::new(|s: i32| (s, s + 1));
    let initial_state = 10;

    // Run and get both value and new state
    let (value, new_state) = counter.run_state(initial_state);
    assert_eq!((value, new_state), (10, 11));

    // Run and get only the value
    let value_only = counter.eval_state(initial_state);
    assert_eq!(value_only, 10);

    // Run and get only the new state
    let state_only = counter.exec_state(initial_state);
    assert_eq!(state_only, 11);
}

#[test]
fn core_state_operations() {
    use rustica::datatypes::state::{State, get, modify, put};

    // get(): Read the state
    let read_state: State<String, String> = get();
    let (value, state) = read_state.run_state("hello".to_string());
    assert_eq!(value, "hello");
    assert_eq!(state, "hello"); // State is unchanged

    // put(): Overwrite the state
    let write_state: State<&str, ()> = put("world");
    let (value, state) = write_state.run_state("hello");
    assert_eq!(value, ()); // put returns a unit value
    assert_eq!(state, "world"); // State is replaced

    // modify(): Update the state
    let update_state: State<i32, ()> = modify(|s| s * 2);
    let (value, state) = update_state.run_state(10);
    assert_eq!(value, ()); // modify returns a unit value
    assert_eq!(state, 20); // State is updated
}

#[test]
fn composing_operations_with_bind() {
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

    assert_eq!(final_value, 20);
    assert_eq!(final_state, 20);
}

#[test]
fn practical_example_a_functional_stack() {
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

    assert_eq!(final_result, (Some(20), Some(10)));
    assert_eq!(final_stack, Vec::<i32>::new());
}
