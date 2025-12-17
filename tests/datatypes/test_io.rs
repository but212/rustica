use rustica::datatypes::io::IO;
use std::sync::Arc;
use std::sync::Mutex;

#[test]
fn test_io_creation_and_run() {
    // Test basic creation and running
    let io = IO::pure(42);
    let result = io.run();
    assert_eq!(result, 42);

    // Test creation with a custom computation
    let computation = IO::new(|| 42);
    assert_eq!(computation.run(), 42);

    // Test with mutable state
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = Arc::clone(&counter);
    let mutable_computation = IO::new(move || {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });

    assert_eq!(mutable_computation.run(), 1);
    assert_eq!(mutable_computation.run(), 2);
}

#[test]
fn test_io_complex_composition() {
    // Create a chain of computations
    let initial = IO::pure(10);
    let step1 = initial.fmap(|x| x * 2); // 20
    let step2 = step1.bind(|x| IO::pure(x + 5)); // 25
    let step3 = step2.fmap(|x| x - 3); // 22

    // Run the final computation
    let result = step3.run();
    assert_eq!(result, 22);
}

#[test]
fn test_io_error_handling() {
    // Simulate error handling with IO
    let safe_div = |n: i32, d: i32| -> IO<Result<i32, String>> {
        IO::pure(if d == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(n / d)
        })
    };

    let result1 = safe_div(10, 2).run();
    assert_eq!(result1, Ok(5));

    let result2 = safe_div(10, 0).run();
    assert_eq!(result2, Err("Division by zero".to_string()));
}

#[test]
fn test_io_shared_state() {
    let counter = Arc::new(Mutex::new(0));

    // Create multiple IO instances that share state
    let increment = {
        let counter = Arc::clone(&counter);
        IO::new(move || {
            let mut count = counter.lock().unwrap();
            *count += 1;
            *count
        })
    };

    let get_count = {
        let counter = Arc::clone(&counter);
        IO::new(move || {
            let count = counter.lock().unwrap();
            *count
        })
    };

    // Test that they correctly share and modify state
    assert_eq!(increment.run(), 1);
    assert_eq!(increment.run(), 2);
    assert_eq!(get_count.run(), 2);
    assert_eq!(increment.run(), 3);
    assert_eq!(get_count.run(), 3);
}

#[test]
fn test_io_monad() {
    let computation = IO::new(|| 42);

    // Test bind
    let doubled = computation.bind(|x| IO::new(move || x * 2));
    assert_eq!(doubled.run(), 84);

    // Test monad laws
    // 1. Left identity: pure(a).bind(f) ≡ f(a)
    let left_identity = IO::pure(42).bind(|x| IO::new(move || x * 2));
    let direct = IO::new(|| 84);
    assert_eq!(left_identity.run(), direct.run());

    // 2. Right identity: m.bind(pure) ≡ m
    let right_identity = computation.bind(IO::pure);
    assert_eq!(right_identity.run(), computation.run());

    // 3. Associativity: m.bind(f).bind(g) ≡ m.bind(|x| f(x).bind(g))
    let assoc_left = computation
        .bind(|x| IO::new(move || x * 2))
        .bind(|x| IO::new(move || x + 1));
    let assoc_right = computation.bind(|x| IO::new(move || x * 2).bind(|y| IO::new(move || y + 1)));
    assert_eq!(assoc_left.run(), assoc_right.run());
}

#[test]
fn test_io_composition() {
    let read_number = IO::new(|| 42);
    let result = read_number
        .bind(|x| IO::new(move || x * 2))
        .bind(|x| IO::new(move || format!("Result: {x}")));

    assert_eq!(result.run(), "Result: 84");
}

#[test]
fn test_io_try_get() {
    let computation = IO::new(|| 42);
    assert_eq!(computation.try_get(), Ok(42));
}

#[test]
fn test_io_apply() {
    let computation = IO::new(|| 42);
    let result = computation.apply(IO::new(move || |x| x * 2));
    assert_eq!(result.run(), 84);
}

#[test]
fn test_io_is_pure() {
    let pure_io = IO::pure(42);
    assert!(pure_io.is_pure());
    assert!(!pure_io.is_effect());

    let effect_io = IO::new(|| 42);
    assert!(!effect_io.is_pure());
    assert!(effect_io.is_effect());
}

#[test]
fn test_io_try_get_with_context_success() {
    let io_success: IO<i32> = IO::pure(42);
    let result = io_success.try_get_with_context("calculating answer");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
}

#[test]
fn test_io_try_get_with_context_failure() {
    let io_fail: IO<i32> = IO::new(|| panic!("computation failed"));
    let result = io_fail.try_get_with_context("critical calculation");
    assert!(result.is_err());

    let error = result.unwrap_err();
    assert_eq!(error.context(), vec!["critical calculation".to_string()]);
}

#[test]
fn test_io_try_get_composable() {
    let io_success = IO::pure(42);
    let result = io_success.try_get_composable();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
}

#[test]
fn test_io_try_get_composable_failure() {
    let io_fail: IO<i32> = IO::new(|| panic!("computation failed"));
    let result = io_fail.try_get_composable();
    assert!(result.is_err());
}

#[test]
fn test_io_try_get_composable_with_context() {
    let io_operation = IO::pure(42).bind(|x| IO::new(move || x * 2));
    let result = io_operation.try_get_composable_with_context("processing data");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 84);
}

#[test]
fn test_io_try_get_composable_with_context_failure() {
    let io_fail: IO<i32> = IO::new(|| panic!("database error"));
    let result = io_fail.try_get_composable_with_context("fetching user data");
    assert!(result.is_err());

    let error = result.unwrap_err();
    assert_eq!(error.context().len(), 1);
    assert!(error.context()[0].contains("fetching user data"));
}

#[test]
fn test_io_into_error_pipeline() {
    let io_operation = IO::pure(42);
    let result = io_operation.into_error_pipeline().finish();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
}

#[test]
fn test_io_recover() {
    let io_risky: IO<i32> = IO::new(|| panic!("primary failed"));
    let io_recovered = io_risky.recover(|_error| IO::pure(0));
    assert_eq!(io_recovered.run(), 0);

    let io_ok = IO::pure(42);
    let io_still_ok = io_ok.recover(|_| IO::pure(0));
    assert_eq!(io_still_ok.run(), 42);
}

#[test]
fn test_io_recover_with() {
    let io_risky: IO<i32> = IO::new(|| panic!("failed"));
    let io_safe = io_risky.recover_with(42);
    assert_eq!(io_safe.run(), 42);

    let io_ok = IO::pure(100);
    let io_still_ok = io_ok.recover_with(42);
    assert_eq!(io_still_ok.run(), 100);
}

#[test]
fn test_io_sequence_composable_success() {
    let ios = vec![IO::pure(1), IO::pure(2), IO::pure(3)];
    let result = IO::sequence_composable(ios);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), vec![1, 2, 3]);
}

#[test]
fn test_io_sequence_composable_with_failures() {
    let ios_mixed = vec![
        IO::pure(1),
        IO::new(|| panic!("error 1")),
        IO::pure(3),
        IO::new(|| panic!("error 2")),
    ];
    let result = IO::sequence_composable(ios_mixed);
    assert!(result.is_err());
}

#[test]
fn test_io_when() {
    let conditional_true = IO::when(|| true, || 42, || 0);
    assert_eq!(conditional_true.run(), 42);

    let conditional_false = IO::when(|| false, || 42, || 0);
    assert_eq!(conditional_false.run(), 0);
}

#[test]
fn test_io_delay_sync() {
    use std::time::{Duration, Instant};

    let start = Instant::now();
    let delayed_io = IO::delay_sync(Duration::from_millis(10), 123);
    let result = delayed_io.run();

    assert_eq!(result, 123);
    assert!(start.elapsed() >= Duration::from_millis(10));
}

#[test]
fn test_io_combine() {
    let io1 = IO::pure(10);
    let io2 = IO::pure(20);
    let combined = IO::combine(&io1, &io2);

    assert_eq!(combined.run(), (10, 20));
}

#[test]
fn test_io_sequence() {
    let ios = vec![IO::pure(1), IO::pure(2), IO::pure(3)];
    let sequenced = IO::sequence(ios);
    assert_eq!(sequenced.run(), vec![1, 2, 3]);
}

#[test]
fn test_io_clone() {
    let io = IO::pure(42);
    let cloned = io.clone();
    assert_eq!(io.run(), cloned.run());

    let effect_io = IO::new(|| 100);
    let cloned_effect = effect_io.clone();
    assert_eq!(effect_io.run(), cloned_effect.run());
}

#[test]
fn test_io_apply_pure_pure() {
    let io_value = IO::pure(10);
    let io_func = IO::pure(|x: i32| x * 2);
    let result = io_value.apply(io_func);
    assert_eq!(result.run(), 20);
}

#[test]
fn test_io_apply_pure_effect() {
    let io_value = IO::pure(5);
    let io_func = IO::new(|| {
        let multiplier = 3;
        move |x: i32| x * multiplier
    });
    let result = io_value.apply(io_func);
    assert_eq!(result.run(), 15);
}

#[test]
fn test_io_apply_effect_pure() {
    let io_value = IO::new(|| 5);
    let io_func = IO::pure(|x: i32| x * 3);
    let result = io_value.apply(io_func);
    assert_eq!(result.run(), 15);
}

#[test]
fn test_io_apply_effect_effect() {
    let io_value = IO::new(|| 5);
    let io_func = IO::new(|| |x: i32| x * 3);
    let result = io_value.apply(io_func);
    assert_eq!(result.run(), 15);
}

#[test]
fn test_io_fmap_pure() {
    let io = IO::pure(42);
    let mapped = io.fmap(|x| x * 2);
    assert_eq!(mapped.run(), 84);
}

#[test]
fn test_io_fmap_effect() {
    let io = IO::new(|| 42);
    let mapped = io.fmap(|x| x * 2);
    assert_eq!(mapped.run(), 84);
}

#[test]
fn test_io_bind_pure() {
    let io = IO::pure(42);
    let bound = io.bind(|x| IO::pure(x + 1));
    assert_eq!(bound.run(), 43);
}

#[test]
fn test_io_bind_effect() {
    let io = IO::new(|| 42);
    let bound = io.bind(|x| IO::pure(x + 1));
    assert_eq!(bound.run(), 43);
}
