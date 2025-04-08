
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
        .bind(|x| IO::new(move || format!("Result: {}", x)));

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
    let result = computation.apply(|x| IO::new(move || x * 2));
    assert_eq!(result.run(), 84);
}
