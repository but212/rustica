use rustica::datatypes::state::{State, get, modify, put};

#[test]
fn test_state_documented_scenarios() {
    let counter = State::new(|s: i32| (s, s + 1));
    assert_eq!(counter.run_state(0), (0, 1));
    assert_eq!(counter.run_state(10), (10, 11));

    let computation = get::<i32>().bind(|x| {
        modify(move |s: i32| s + x)
            .bind(|_| get::<i32>().bind(|y| put(y * 2).bind(move |_| State::pure(y))))
    });
    assert_eq!(computation.run_state(2), (4, 8));

    fn push<T: Send + Sync + Clone + 'static>(x: T) -> State<Vec<T>, ()> {
        State::new(move |mut stack: Vec<T>| {
            stack.push(x.clone());
            ((), stack)
        })
    }
    fn pop<T: Send + Sync + Clone + 'static>() -> State<Vec<T>, Option<T>> {
        State::new(|mut stack: Vec<T>| (stack.pop(), stack))
    }
    let stack_ops = push(1)
        .bind(|_| push(2))
        .bind(|_| push(3))
        .bind(|_| pop::<i32>())
        .bind(|x| pop::<i32>().bind(move |y| State::pure((x, y))));
    assert_eq!(
        stack_ops.run_state(Vec::new()),
        ((Some(3), Some(2)), vec![1])
    );
}

#[test]
fn test_state_monadic_laws_and_execution() {
    let state = State::new(|s: i32| (s * 2, s + 1));
    assert_eq!(state.run_state(5), (10, 6));
    assert_eq!(state.eval_state(5), 10);
    assert_eq!(state.exec_state(5), 6);

    let pure_val = State::pure(42);
    assert_eq!(pure_val.run_state(0), (42, 0));
    let mapped = State::new(|s: i32| (s, s + 1)).fmap(|x| x * 2);
    assert_eq!(mapped.run_state(10), (20, 11));
    let bound = State::new(|s: i32| (s, s + 1)).bind(|x| State::new(move |s| (x + s, s * 2)));
    assert_eq!(bound.run_state(5), (11, 12));
}
