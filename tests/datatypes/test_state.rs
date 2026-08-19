use rustica::datatypes::state::State;

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
