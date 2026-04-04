use rustica::traits::monad_error::{ErrorMapper, MonadError};

#[test]
fn test_monad_error_laws_and_interop() {
    // 1. Left Catch Law: throw(e).catch(h) == h(e)
    let err = "err".to_string();
    let thrown: Result<i32, String> = Result::<i32, String>::throw(err.clone());
    let handled = thrown.catch(|e| if e == "err" { Ok(42) } else { Err(e.clone()) });
    assert_eq!(handled, Ok(42));

    // 2. Right Catch Law: m.catch(throw) == m
    let m: Result<i32, String> = Ok(10);
    let caught_m = m.catch(|e| Result::<i32, String>::throw(e.clone()));
    assert_eq!(caught_m, m);

    // 3. Option Interop: throw(()) == None
    let thrown_none: Option<i32> = Option::<i32>::throw(());
    assert_eq!(thrown_none, None);
    assert_eq!(None.catch(|_| Some(0)), Some(0));
}

#[test]
fn test_error_mapping_and_transformation() {
    // 1. Structural error mapping
    let result: Result<i32, String> = Err("404".to_string());
    let mapped = result.map_error_to(|e: &String| format!("E:{}", e));
    assert_eq!(mapped, Err("E:404".to_string()));

    // 2. Multi-step transformation
    let twice = result
        .map(|x| x * 2)
        .map_error_to(|e| format!("Error on {}", e));
    assert_eq!(twice, Err("Error on 404".to_string()));
}

#[test]
fn test_monad_error_workflow_scenarios() {
    #[derive(Debug, Clone, PartialEq)]
    struct AppError { msg: String }

    let result: Result<i32, AppError> = Result::<i32, AppError>::throw(AppError { msg: "invalid".into() });

    // Full chain: throw -> catch specific -> map the rest
    let handled = result
        .catch(|e| {
            if e.msg == "retryable" { Ok(0) } else { Err(e.clone()) }
        })
        .map_error_to(|e| format!("Final: {}", e.msg));

    assert_eq!(handled, Err("Final: invalid".to_string()));
}
