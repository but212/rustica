use rustica::transformers::StateT;

#[test]
fn test_state_t_creation_and_running() {
    // Create a simple StateT that increments the state and returns the old state
    let state_t: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| Some((s + 1, s)));

    // Run with an initial state
    let result = state_t.run_state(5);
    assert_eq!(result, Some((6, 5)));
}

#[test]
fn test_state_t_composition() {
    // Create a StateT that adds 1 to the state
    let add_one: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| Some((s + 1, s + 1)));

    // Create a StateT that multiplies the state by 2
    let double: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| Some((s * 2, s)));

    // Capture a clone of double to avoid ownership issues
    let double_clone = double.clone();

    // Compose operations using bind_with
    let add_then_double = add_one.bind_with(
        move |_| double_clone.clone(),
        |m: Option<(i32, i32)>, f| m.and_then(|(s, _)| f((s, 0))),
    );

    // Run the composed operation with an initial state
    let result = add_then_double.run_state(5);

    // After adding 1, state = 6, then we double it to 12
    // The final result pair is (12, 6) where 6 is the state after the first operation
    assert_eq!(result, Some((12, 6)));
}

#[test]
fn test_state_t_get_and_put() {
    // Create a StateT that gets the current state
    let get_state = StateT::<i32, Option<(i32, i32)>, i32>::get(Some);

    // Create a StateT that sets a new state
    let set_state = StateT::<i32, Option<(i32, i32)>, i32>::put(42, Some);

    // Run these operations
    let get_result = get_state.run_state(10);
    let put_result = set_state.run_state(10);

    assert_eq!(get_result, Some((10, 10))); // State unchanged, returns state
    assert_eq!(put_result, Some((42, 10))); // State changed to 42, returns old state
}

#[test]
fn test_state_t_modify() {
    // Create a StateT that doubles the current state
    let double_state = StateT::<i32, Option<(i32, ())>, ()>::modify(|s| s * 2, Some);

    // Run the operation
    let result = double_state.run_state(21);

    assert_eq!(result, Some((42, ()))); // State doubled, returns unit
}

#[test]
fn test_state_t_with_error_handling() {
    // Create a StateT that fails when the state is 0
    let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
        if s == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok((s, 100 / s))
        }
    });

    // Run with valid and invalid states
    let success = safe_div.run_state(4);
    let failure = safe_div.run_state(0);

    assert_eq!(success, Ok((4, 25))); // 100/4 = 25
    assert_eq!(failure, Err("Division by zero".to_string()));
}

#[test]
fn test_state_t_standardized_error_handling() {
    // Create a StateT that fails when the state is 0
    let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
        if s == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok((s, 100 / s))
        }
    });

    // Test try_run_state with success case
    let result = safe_div.try_run_state(4);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), (4, 25)); // 100/4 = 25

    // Test try_run_state with error case
    let result = safe_div.try_run_state(0);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message(), &"Division by zero");

    // Test try_run_state_with_context with success case
    let result = safe_div.try_run_state_with_context(4, "processing user input");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), (4, 25));

    // Test try_run_state_with_context with error case
    let result = safe_div.try_run_state_with_context(0, "processing user input");
    assert!(result.is_err());
    let error = result.unwrap_err();
    assert_eq!(error.message(), &"Division by zero");
    assert_eq!(error.context(), Some(&"processing user input"));

    // Test try_eval_state (only returns the value)
    let result = safe_div.try_eval_state(4);
    assert_eq!(result, Ok(25));

    let result = safe_div.try_eval_state(0);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message(), &"Division by zero");

    // Test try_eval_state_with_context
    let result = safe_div.try_eval_state_with_context(4, "evaluating result");
    assert_eq!(result, Ok(25));

    let result = safe_div.try_eval_state_with_context(0, "evaluating result");
    assert!(result.is_err());
    let error = result.unwrap_err();
    assert_eq!(error.message(), &"Division by zero");
    assert_eq!(error.context(), Some(&"evaluating result"));

    // Create a StateT that modifies the state and may fail
    let modify_and_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
        if s == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok((s + 1, 100 / s))
        }
    });

    // Test try_exec_state (only returns the state)
    let result = modify_and_div.try_exec_state(4);
    assert_eq!(result, Ok(5)); // state: 4 + 1 = 5

    let result = modify_and_div.try_exec_state(0);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message(), &"Division by zero");

    // Test map_error to transform error types
    let mapped = safe_div.map_error(|e: String| e.len() as i32);

    // The error is now the length of the original error string
    let result = mapped.run_state(0);
    assert_eq!(result, Err(16)); // "Division by zero" has length 16

    // Success case still works
    let result = mapped.run_state(5);
    assert_eq!(result, Ok((5, 20))); // 100/5 = 20
}

#[test]
fn test_state_t_with_complex_error_handling() {
    // Define a more complex state type
    #[derive(Debug, Clone, PartialEq)]
    struct Counter {
        value: i32,
        operations: i32,
    }

    // Create a series of operations that might fail
    let increment_if_valid: StateT<Counter, Result<(Counter, i32), String>, i32> =
        StateT::new(|mut s: Counter| {
            if s.value < 0 {
                Err("Cannot increment a negative counter".to_string())
            } else {
                s.value += 1;
                s.operations += 1;
                Ok((s.clone(), s.value))
            }
        });

    let double_if_even: StateT<Counter, Result<(Counter, i32), String>, i32> =
        StateT::new(|mut s: Counter| {
            if s.value % 2 != 0 {
                Err("Cannot double an odd value".to_string())
            } else {
                let old_value = s.value;
                s.value *= 2;
                s.operations += 1;
                Ok((s.clone(), old_value))
            }
        });

    // Test the first operation with try_run_state
    let mut counter = Counter {
        value: 5,
        operations: 0,
    };
    let result = increment_if_valid.try_run_state(counter.clone());
    assert!(result.is_ok());
    let (new_counter, value) = result.unwrap();
    assert_eq!(value, 6);
    assert_eq!(new_counter.operations, 1);
    counter = new_counter;

    // The second operation should now succeed because the value is 6 (even)
    let result = double_if_even.try_run_state(counter.clone());
    assert!(result.is_ok());
    let (final_counter, value) = result.unwrap();
    assert_eq!(value, 6); // The old value
    assert_eq!(final_counter.value, 12); // Doubled from 6
    assert_eq!(final_counter.operations, 2); // 1 from increment + 1 from double

    // Let's also verify that with an odd value, it fails as expected
    let odd_counter = Counter {
        value: 7,
        operations: 0,
    };
    let result = double_if_even.try_run_state(odd_counter);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().message(), &"Cannot double an odd value");
}
