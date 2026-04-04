use rustica::datatypes::state::{State, get, modify, put};

#[test]
fn test_state_monadic_laws_and_execution() {
    // 1. Core Anatomy (run, eval, exec)
    let state = State::new(|s: i32| (s * 2, s + 1));
    assert_eq!(state.run_state(5), (10, 6));
    assert_eq!(state.eval_state(5), 10);
    assert_eq!(state.exec_state(5), 6);

    // 2. Functor & Monad Laws
    let pure_val = State::pure(42);
    assert_eq!(pure_val.run_state(0), (42, 0));

    // fmap: (s+1) -> (s+1)*2
    let mapped = State::new(|s: i32| (s, s + 1)).fmap(|x| x * 2);
    assert_eq!(mapped.run_state(10), (20, 11));

    // bind: chaining dependent computations
    let bound = State::new(|s: i32| (s, s + 1)).bind(|x| State::new(move |s| (x + s, s * 2)));
    assert_eq!(bound.run_state(5), (11, 12));
}

#[test]
fn test_state_primitives_and_applicative() {
    // 1. Basic primitives (get, put, modify)
    let ops = get::<i32>()
        .bind(|x| modify(move |s: i32| s + x))
        .bind(|_| get::<i32>())
        .bind(|y| put(y * 2).fmap(move |_| y));

    assert_eq!(ops.run_state(2), (4, 8));

    // 2. Applicative: apply
    let add_state = State::new(|s: i32| (move |x: i32| x + s, s + 1));
    let val_state = State::new(|s: i32| (s * 2, s + 2));
    let result = add_state.apply(val_state);

    // (5*2) + 5 = 15, State: (5+2)+1 = 8 ? No, sequential:
    // add_state run(5) -> (f, 6), then val_state run(6) -> (12, 8), then f(12) = 17
    assert_eq!(result.run_state(5), (17, 8));
}

#[test]
fn test_state_resilience_and_errors() {
    let fallible: State<i32, Result<i32, &str>> = State::new(|s| {
        if s > 0 {
            (Ok(s * 10), s + 1)
        } else {
            (Err("negative"), s)
        }
    });

    // 1. Success case with context
    let (res1, s1) = fallible.try_run_state_with_context(5, "ctx");
    assert_eq!(res1, Ok(50));
    assert_eq!(s1, 6);

    // 2. Failure case with context and eval/exec equivalence
    let (res2, s2) = fallible.try_run_state_with_context(-1, "ctx");
    assert!(res2.is_err());
    assert_eq!(res2.unwrap_err().context(), vec!["ctx".to_string()]);
    assert_eq!(s2, -1);

    assert!(fallible.try_eval_state(-1).is_err());
    assert_eq!(fallible.try_exec_state(5), Ok(6));
}

#[test]
fn test_state_complex_scenarios() {
    // 1. Stack Operations
    let push = |x: i32| {
        modify(move |mut s: Vec<i32>| {
            s.push(x);
            s
        })
    };
    let pop = State::new(|mut s: Vec<i32>| (s.pop(), s));

    let stack_logic = push(1).bind(move |_| push(2)).bind(move |_| pop.clone());
    assert_eq!(stack_logic.run_state(vec![]), (Some(2), vec![1]));

    // 2. Fibonacci Generation
    let next_fib = get::<(u32, u32)>().bind(|(a, b)| put((b, a + b)).bind(move |_| State::pure(a)));

    let mut state = (0, 1);
    let mut results = vec![];
    for _ in 0..5 {
        results.push(next_fib.eval_state(state));
        state = next_fib.exec_state(state);
    }
    assert_eq!(results, vec![0, 1, 1, 2, 3]);

    // 3. String State manipulation
    let string_op = modify(|s: String| s + " world").bind(|_| get::<String>());
    assert_eq!(
        string_op.run_state("hello".into()),
        ("hello world".into(), "hello world".into())
    );
}
