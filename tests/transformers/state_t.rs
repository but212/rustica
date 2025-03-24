use rustica::transformers::StateT;

#[test]
fn test_state_t_creation_and_running() {
    // Create a simple StateT that increments the state and returns the old state
    let state_t: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
        Some((s + 1, s))
    });
    
    // Run with an initial state
    let result = state_t.run_state(5);
    assert_eq!(result, Some((6, 5)));
}

#[test]
fn test_state_t_composition() {
    // Create a StateT that adds 1 to the state
    let add_one: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
        Some((s + 1, s + 1))
    });
    
    // Create a StateT that multiplies the state by 2
    let double: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
        Some((s * 2, s))
    });
    
    // Capture a clone of double to avoid ownership issues
    let double_clone = double.clone();
    
    // Compose operations using bind_with
    let add_then_double = add_one.bind_with(
        move |_| double_clone.clone(),
        |m: Option<(i32, i32)>, f| m.and_then(|(s, _)| f((s, 0))) 
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
    
    assert_eq!(success, Ok((4, 25)));       // 100/4 = 25
    assert_eq!(failure, Err("Division by zero".to_string()));
}
