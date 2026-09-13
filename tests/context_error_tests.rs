use rustica::context;
use rustica::error::{ContextError, accumulate_context, with_context, with_context_result};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn test_context_error_creation() {
    let err = ContextError::new("file not found");
    assert_eq!(err.error(), &"file not found");
    assert_eq!(err.into_error(), "file not found");
}

#[test]
fn test_context_error_stack() {
    let err = ContextError::new("db connection failed")
        .with_context("query failed")
        .with_context("user lookup failed");

    assert_eq!(err.error(), &"db connection failed");
    assert_eq!(
        err.context(),
        vec!["user lookup failed".to_string(), "query failed".to_string()]
    );

    let collected: Vec<_> = err.context_iter().map(String::as_str).collect();
    assert_eq!(collected, vec!["user lookup failed", "query failed"]);
}

#[test]
fn test_context_error_formatting() {
    let err = ContextError::new("connection refused")
        .with_context("database error")
        .with_context("application start failed");

    assert_eq!(
        err.error_chain(),
        "application start failed -> database error -> connection refused"
    );
    assert_eq!(
        format!("{err}"),
        "application start failed -> database error -> connection refused"
    );
}

#[test]
fn test_lazy_context_evaluation() {
    let was_evaluated = Arc::new(AtomicBool::new(false));
    let was_evaluated_clone = was_evaluated.clone();
    let result: Result<i32, &str> = Ok(42);

    let res = with_context_result(
        result,
        context!("This should not be evaluated: {}", {
            was_evaluated_clone.store(true, Ordering::SeqCst);
            "failed"
        }),
    );

    assert_eq!(res, Ok(42));
    assert!(!was_evaluated.load(Ordering::SeqCst));
}

#[test]
fn test_lazy_context_evaluation_on_error() {
    let was_evaluated = Arc::new(AtomicBool::new(false));
    let was_evaluated_clone = was_evaluated.clone();
    let result: Result<i32, &str> = Err("underlying error");

    let res = with_context_result(
        result,
        context!("Context evaluated: {}", {
            was_evaluated_clone.store(true, Ordering::SeqCst);
            "yes"
        }),
    );

    assert!(was_evaluated.load(Ordering::SeqCst));
    match res {
        Err(err) => {
            assert_eq!(err.error(), &"underlying error");
            assert_eq!(err.context(), vec!["Context evaluated: yes".to_string()]);
        },
        Ok(_) => panic!("expected error"),
    }
}

#[test]
fn test_with_context_and_accumulate() {
    let err = with_context("disk full", "save document");
    assert_eq!(err.error(), &"disk full");
    assert_eq!(err.context(), vec!["save document".to_string()]);

    let accumulated =
        accumulate_context("network timeout", ["attempt 1 failed", "attempt 2 failed"]);
    assert_eq!(accumulated.error(), &"network timeout");
    assert_eq!(
        accumulated.context(),
        vec![
            "attempt 2 failed".to_string(),
            "attempt 1 failed".to_string()
        ]
    );
}

#[test]
fn test_context_error_map_error_and_from() {
    let err = ContextError::new(404).with_context("not found");
    let mapped = err.map_error(|code| format!("HTTP {code}"));
    assert_eq!(mapped.error(), "HTTP 404");
    assert_eq!(mapped.context(), vec!["not found".to_string()]);

    let from_err: ContextError<&str> = "raw error".into();
    assert_eq!(from_err.error(), &"raw error");
    assert!(from_err.context().is_empty());
}

#[test]
fn test_context_error_source_chain() {
    use std::error::Error;
    let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "file not found");
    let ctx_err = ContextError::new(io_err).with_context("reading config");

    let std_err: &dyn Error = &ctx_err;
    assert!(std_err.source().is_some());
    let src = std_err.source().unwrap();
    assert_eq!(src.to_string(), "file not found");
}

#[test]
fn test_context_error_raw_slice() {
    let err = ContextError::new("core")
        .with_context("first")
        .with_context("second");

    assert_eq!(
        err.contexts_raw(),
        &["first".to_string(), "second".to_string()]
    );
}
