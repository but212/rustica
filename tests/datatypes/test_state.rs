//! Tests for the State monad

use rustica::datatypes::state::{State, get, modify, put};

mod basic_operations {
    use super::*;

    #[test]
    fn test_new_and_run_state() {
        let counter = State::new(|s: i32| (s, s + 1));
        assert_eq!(counter.run_state(0), (0, 1));
        assert_eq!(counter.run_state(10), (10, 11));
    }

    #[test]
    fn test_eval_state() {
        let counter = State::new(|s: i32| (s * 2, s + 1));
        assert_eq!(counter.eval_state(5), 10);
        assert_eq!(counter.eval_state(0), 0);
    }

    #[test]
    fn test_exec_state() {
        let counter = State::new(|s: i32| (s * 2, s + 1));
        assert_eq!(counter.exec_state(5), 6);
        assert_eq!(counter.exec_state(0), 1);
    }

    #[test]
    fn test_exec_pure() {
        let state = State::new(|s: i32| (s * 2, s + 1));
        let result = state.exec_pure(42);
        assert_eq!(result, 43);
    }

    #[test]
    fn test_pure() {
        let computation: State<i32, &str> = State::pure("hello");
        assert_eq!(computation.run_state(42), ("hello", 42));
        assert_eq!(computation.run_state(0), ("hello", 0));
    }

    #[test]
    fn test_clone() {
        let counter = State::new(|s: i32| (s, s + 1));
        let cloned = counter.clone();
        assert_eq!(counter.run_state(5), cloned.run_state(5));
    }
}

mod functor_operations {
    use super::*;

    #[test]
    fn test_fmap() {
        let counter = State::new(|s: i32| (s, s + 1));
        let doubled = counter.fmap(|x| x * 2);
        assert_eq!(doubled.run_state(5), (10, 6));
    }

    #[test]
    fn test_functor_identity_law() {
        let state = State::new(|s: i32| (s * 2, s + 1));
        let identity = |x: i32| x;
        let mapped = state.clone().fmap(identity);
        assert_eq!(state.run_state(5), mapped.run_state(5));
    }

    #[test]
    fn test_functor_composition_law() {
        let state = State::new(|s: i32| (s, s + 1));
        let f = |x: i32| x * 3;
        let g = |x: i32| x + 2;

        let composed = state.clone().fmap(move |x| f(g(x)));
        let chained = state.clone().fmap(g).fmap(f);

        assert_eq!(composed.run_state(10), chained.run_state(10));
    }
}

mod monad_operations {
    use super::*;

    #[test]
    fn test_bind() {
        let counter = State::new(|s: i32| (s, s + 1));
        let computation = counter.bind(|x| State::new(move |s| (x + s, s * 2)));

        assert_eq!(computation.run_state(5), (11, 12));
    }

    #[test]
    fn test_monad_left_identity_law() {
        let value = 10;
        let f = |x: i32| State::new(move |s: i32| (x * 2, s + 1));

        let left_side = State::pure(value).bind(f);
        let right_side = f(value);

        assert_eq!(left_side.run_state(5), right_side.run_state(5));
    }

    #[test]
    fn test_monad_right_identity_law() {
        let m = State::new(|s: i32| (s * 3, s + 2));
        let right_side = m.clone().bind(State::pure);

        assert_eq!(m.run_state(5), right_side.run_state(5));
    }

    #[test]
    fn test_monad_associativity_law() {
        let m = State::new(|s: i32| (s, s + 1));
        let f = |x: i32| State::new(move |s: i32| (x * 2, s + 5));
        let g = |x: i32| State::new(move |s: i32| (x + 10, s * 2));

        let left_side = m.clone().bind(f).bind(g);
        let right_side = m.clone().bind(move |x| f(x).bind(g));

        assert_eq!(left_side.run_state(3), right_side.run_state(3));
    }

    #[test]
    fn test_bind_conditional() {
        let counter = State::new(|s: i32| (s, s + 1));
        let computation = counter.bind(|x| {
            if x % 2 == 0 {
                State::new(move |s| (format!("Even: {}", x), s * 2))
            } else {
                State::new(move |s| (format!("Odd: {}", x), s + 10))
            }
        });

        assert_eq!(computation.run_state(4), ("Even: 4".to_string(), 10));
        assert_eq!(computation.run_state(5), ("Odd: 5".to_string(), 16));
    }
}

mod applicative_operations {
    use super::*;

    #[test]
    fn test_apply() {
        let add_one: State<i32, fn(i32) -> i32> = State::pure(|x: i32| x + 1);
        let value: State<i32, i32> = State::pure(41);

        let result = add_one.apply(value);
        assert_eq!(result.run_state(0), (42, 0));
    }

    #[test]
    fn test_apply_with_state_changes() {
        let add_state = State::new(|state: i32| (move |x: i32| x + state, state + 1));
        let value = State::new(|s: i32| (s * 2, s + 2));

        let result = add_state.apply(value);
        assert_eq!(result.run_state(5), (17, 8));
    }
}

mod utility_functions {
    use super::*;

    #[test]
    fn test_get() {
        let computation = get::<i32>();
        assert_eq!(computation.run_state(42), (42, 42));
        assert_eq!(computation.run_state(0), (0, 0));
    }

    #[test]
    fn test_put() {
        let computation = put(42);
        assert_eq!(computation.run_state(0), ((), 42));
        assert_eq!(computation.run_state(100), ((), 42));
    }

    #[test]
    fn test_modify() {
        let increment = modify(|x: i32| x + 1);
        assert_eq!(increment.run_state(41), ((), 42));

        let double = modify(|x: i32| x * 2);
        assert_eq!(double.run_state(21), ((), 42));
    }

    #[test]
    fn test_get_put_modify_composition() {
        let computation = get::<i32>().bind(|x| {
            let x_captured = x;
            modify(move |s: i32| s + x_captured)
                .bind(move |_| get::<i32>().bind(move |y| put(y * 2).bind(move |_| State::pure(y))))
        });

        assert_eq!(computation.run_state(2), (4, 8));
    }

    #[test]
    fn test_chained_state_operations() {
        let add_5 = modify(|s: i32| s + 5);
        let multiply_by_2 = modify(|s: i32| s * 2);
        let subtract_3 = modify(|s: i32| s - 3);

        let apply_operations = vec![add_5, multiply_by_2, subtract_3]
            .into_iter()
            .fold(State::pure(()), |acc, op| acc.bind(move |_| op.clone()));

        assert_eq!(apply_operations.exec_state(0), 7);
    }
}

mod error_handling {
    use super::*;

    #[test]
    fn test_try_run_state_success() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let (result, final_state) = state.try_run_state(5);
        assert_eq!(result, Ok(10));
        assert_eq!(final_state, 6);
    }

    #[test]
    fn test_try_run_state_failure() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let (result, final_state) = state.try_run_state(-1);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().core_error(), &"Value must be positive");
        assert_eq!(final_state, -1);
    }

    #[test]
    fn test_try_run_state_with_context() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let (result, final_state) = state.try_run_state_with_context(5, "processing user input");
        assert_eq!(result, Ok(10));
        assert_eq!(final_state, 6);

        let (result, final_state) = state.try_run_state_with_context(-1, "processing user input");
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(error.core_error(), &"Value must be positive");
        assert_eq!(error.context(), vec!["processing user input".to_string()]);
        assert_eq!(final_state, -1);
    }

    #[test]
    fn test_try_eval_state() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let result = state.try_eval_state(5);
        assert_eq!(result, Ok(10));

        let result = state.try_eval_state(-1);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().core_error(), &"Value must be positive");
    }

    #[test]
    fn test_try_eval_state_with_context() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let result = state.try_eval_state_with_context(5, "processing");
        assert_eq!(result, Ok(10));

        let result = state.try_eval_state_with_context(-1, "processing");
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(error.context(), vec!["processing".to_string()]);
    }

    #[test]
    fn test_try_exec_state() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let final_state = state.try_exec_state(5);
        assert_eq!(final_state, Ok(6));

        let final_state = state.try_exec_state(-1);
        assert!(final_state.is_err());
        assert_eq!(
            final_state.unwrap_err().core_error(),
            &"Value must be positive"
        );
    }

    #[test]
    fn test_try_exec_state_with_context() {
        let state: State<i32, Result<i32, &str>> = State::new(|s: i32| {
            if s > 0 {
                (Ok(s * 2), s + 1)
            } else {
                (Err("Value must be positive"), s)
            }
        });

        let final_state = state.try_exec_state_with_context(5, "processing");
        assert_eq!(final_state, Ok(6));

        let final_state = state.try_exec_state_with_context(-1, "processing");
        assert!(final_state.is_err());
        let error = final_state.unwrap_err();
        assert_eq!(error.context(), vec!["processing".to_string()]);
    }
}

mod conversion {
    use super::*;
    use rustica::datatypes::id::Id;
    use rustica::transformers::state_t::StateT;

    #[test]
    fn test_from_state_t() {
        let state_t: StateT<i32, Id<(i32, i32)>, i32> = StateT::new(|s| Id::new((s + 1, s + 1)));
        let state: State<i32, i32> = State::from(state_t);
        assert_eq!(state.run_state(1), (2, 2));
    }
}

mod complex_scenarios {
    use super::*;

    #[test]
    fn test_stack_operations() {
        fn push<T: Send + Sync + Clone + 'static>(x: T) -> State<Vec<T>, ()> {
            State::new(move |mut stack: Vec<T>| {
                stack.push(x.clone());
                ((), stack)
            })
        }

        fn pop<T: Send + Sync + Clone + 'static>() -> State<Vec<T>, Option<T>> {
            State::new(|mut stack: Vec<T>| {
                let item = stack.pop();
                (item, stack)
            })
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
    fn test_fibonacci_with_state() {
        let fibonacci =
            get::<(u32, u32)>().bind(|(a, b)| put((b, a + b)).bind(move |_| State::pure(a)));

        let mut results = Vec::new();
        let mut state = (0, 1);

        for _ in 0..10 {
            let value = fibonacci.eval_state(state);
            results.push(value);
            state = fibonacci.exec_state(state);
        }

        assert_eq!(results, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_counter_with_string_state() {
        let computation = get::<String>().bind(|current| {
            let current_clone = current.clone();
            modify(|s: String| s + " world").bind(move |_| {
                get::<String>().fmap({
                    let value = current_clone.clone();
                    move |final_val| (value.clone(), final_val)
                })
            })
        });

        let initial = "hello".to_string();
        let ((old, new), final_state) = computation.run_state(initial);
        assert_eq!(old, "hello");
        assert_eq!(new, "hello world");
        assert_eq!(final_state, "hello world");
    }
}
