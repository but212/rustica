use rustica::datatypes::io::IO;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[test]
fn test_io_monadic_fundamentals() {
    // 1. Creation and Purity check
    let pure_io = IO::pure(42);
    let effect_io = IO::new(|| 42);
    assert!(pure_io.is_pure() && effect_io.is_effect());

    // 2. Monad Laws (Representative cases)
    let f = |x: i32| IO::pure(x * 2);
    assert_eq!(IO::pure(10).bind(f).run(), 20); // Left Identity
    assert_eq!(pure_io.clone().bind(IO::pure).run(), 42); // Right Identity

    // 3. Applicative (Effect * Pure combination)
    let val = IO::pure(5);
    let app_f = IO::new(|| {
        let multiplier = 3;
        move |x: i32| x * multiplier
    });
    assert_eq!(val.apply(app_f).run(), 15);

    // 4. Functor & Chaining
    let complex = pure_io.fmap(|x| x + 8).bind(|x| IO::new(move || x / 2));
    assert_eq!(complex.run(), 25);
}

#[test]
fn test_io_shared_state() {
    let counter = Arc::new(Mutex::new(0));
    let increment = {
        let counter = Arc::clone(&counter);
        IO::new(move || {
            let mut count = counter.lock().unwrap();
            *count += 1;
            *count
        })
    };

    assert_eq!(increment.run(), 1);
    assert_eq!(increment.run(), 2);
    assert_eq!(*counter.lock().unwrap(), 2);
}

#[test]
fn test_io_resilience_and_recovery() {
    // 1. Contextual Error Handling (Panic recovery)
    let risky: IO<i32> = IO::new(|| panic!("boom"));
    let result = risky.try_get_with_context("critical task");
    assert!(result.is_err());
    assert!(
        result
            .unwrap_err()
            .context()
            .contains(&"critical task".to_string())
    );

    // 2. Recovery mechanisms
    let recovered = IO::<i32>::new(|| panic!("fail")).recover(|_| IO::pure(0));
    let recovered_with = IO::<i32>::new(|| panic!("fail")).recover_with(42);
    assert_eq!(recovered.run(), 0);
    assert_eq!(recovered_with.run(), 42);

    // 3. Error Pipeline
    let pipeline_res = IO::pure(100).into_error_pipeline().finish();
    assert_eq!(pipeline_res.unwrap(), 100);
}

#[test]
fn test_io_utilities_and_batching() {
    // 1. Batching (Sequence & Combine)
    let ios = vec![IO::pure(1), IO::pure(2)];
    assert_eq!(IO::sequence(ios).run(), vec![1, 2]);
    assert_eq!(IO::combine(&IO::pure(10), &IO::pure(20)).run(), (10, 20));

    // 2. Control Flow: when
    assert_eq!(IO::when(|| true, || 1, || 0).run(), 1);
    assert_eq!(IO::when(|| false, || 1, || 0).run(), 0);

    // 3. Timing: delay_sync
    let start = Instant::now();
    assert_eq!(IO::delay_sync(Duration::from_millis(10), 123).run(), 123);
    assert!(start.elapsed() >= Duration::from_millis(10));
}
