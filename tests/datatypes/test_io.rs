use rustica::datatypes::io::IO;

#[cfg(feature = "async")]
use std::sync::{
    Arc, Barrier,
    atomic::{AtomicUsize, Ordering},
};

#[test]
fn test_io_monadic_fundamentals() {
    let pure_io = IO::pure(42);
    let effect_io = IO::new(|| 42);
    assert!(pure_io.is_pure() && effect_io.is_effect());

    let f = |x: i32| IO::pure(x * 2);
    assert_eq!(IO::pure(10).bind(f).run(), 20);
    assert_eq!(IO::pure(42).bind(IO::pure).run(), 42);

    let val = IO::pure(5);
    let app_f = IO::new(|| {
        let multiplier = 3;
        move |x: i32| x * multiplier
    });
    assert_eq!(val.apply(app_f).run(), 15);

    let complex = pure_io.fmap(|x| x + 8).bind(|x| IO::new(move || x / 2));
    assert_eq!(complex.run(), 25);
}

#[cfg(feature = "async")]
#[test]
fn new_async_run_uses_its_shared_runtime() {
    assert_eq!(IO::new_async(async { 42 }).run(), 42);
}

#[cfg(feature = "async")]
#[test]
fn new_async_concurrent_runs_wait_for_one_initialization() {
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let executions = Arc::new(AtomicUsize::new(0));
    let io = Arc::new(IO::new_async({
        let started = started.clone();
        let release = release.clone();
        let executions = executions.clone();
        async move {
            executions.fetch_add(1, Ordering::SeqCst);
            started.wait();
            release.wait();
            42
        }
    }));

    let first_io = io.clone();
    let first = std::thread::spawn(move || first_io.run());
    started.wait();

    let second_io = io.clone();
    let second = std::thread::spawn(move || second_io.run());
    release.wait();

    assert_eq!(first.join().unwrap(), 42);
    assert_eq!(second.join().unwrap(), 42);
    assert_eq!(executions.load(Ordering::SeqCst), 1);
}

#[test]
fn test_io_execution_and_try_get_composable() {
    let io = IO::pure(100);
    assert_eq!(io.run(), 100);
    assert_eq!(io.try_get_composable(), Ok(100));

    let effect = IO::new(|| 200);
    assert_eq!(effect.run(), 200);
    assert_eq!(effect.try_get_composable(), Ok(200));

    let panicking: IO<i32> = IO::new(|| panic!("failure"));
    assert!(panicking.try_get_composable().is_err());
}
