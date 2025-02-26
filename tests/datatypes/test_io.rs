use rustica::datatypes::io::IO;
use std::sync::Arc;

#[test]
fn test_io_creation_and_run() {
    let computation = IO::new(|| 42);
    assert_eq!(computation.run(), 42);

    let counter = Arc::new(std::sync::Mutex::new(0));
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
fn test_io_functor() {
    let computation = IO::new(|| 42);
    let doubled = computation.fmap(|x| x * 2);
    assert_eq!(doubled.run(), 84);

    let string_length = computation.fmap(|x| x.to_string()).fmap(|s| s.len());
    assert_eq!(string_length.run(), 2);
}

#[test]
fn test_io_pure() {
    let pure_int = IO::pure(42);
    let pure_string = IO::pure("hello".to_string());
    assert_eq!(pure_int.run(), 42);
    assert_eq!(pure_string.run(), "hello");
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
    let assoc_right = computation.bind(|x| {
        IO::new(move || x * 2).bind(|y| IO::new(move || y + 1))
    });
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
fn test_io_error_handling() {
    let computation = IO::new(|| -> Result<i32, &str> {
        Ok(42)
    });

    let result = computation
        .fmap(|r| r.map(|x| x * 2))
        .run();

    assert_eq!(result, Ok(84));

    let failing = IO::new(|| -> Result<i32, &str> {
        Err("Something went wrong")
    });

    let error = failing
        .fmap(|r| r.map(|x| x * 2))
        .run();

    assert_eq!(error, Err("Something went wrong"));
}

#[test]
fn test_io_shared_state() {
    let counter = Arc::new(std::sync::Mutex::new(0));
    let counter_clone = Arc::clone(&counter);

    let increment = IO::new(move || {
        let mut count = counter.lock().unwrap();
        *count += 1;
        *count
    });

    let get_count = IO::new(move || {
        let count = counter_clone.lock().unwrap();
        *count
    });

    assert_eq!(increment.run(), 1);
    assert_eq!(increment.run(), 2);
    assert_eq!(get_count.run(), 2);
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
