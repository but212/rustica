use rustica::context;
use rustica::error::{ContextError, accumulate_context, with_context, with_context_result};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn test_context_error_creation() {
    let err = ContextError::new("file not found");
    assert_eq!(*err.error(), "file not found");
    assert_eq!(err.into_error(), "file not found");
}

#[test]
fn test_context_error_stack() {
    let err = ContextError::new("db connection failed")
        .with_context("query failed")
        .with_context("user lookup failed");

    assert_eq!(*err.error(), "db connection failed");
    assert_eq!(
        err.contexts(),
        ["user lookup failed", "query failed"].as_slice()
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
        "application start failed -> database error"
    );
    assert_eq!(
        format!("{err}"),
        "application start failed -> database error"
    );
}

#[test]
fn test_lazy_context_evaluation() {
    let was_evaluated = Arc::new(AtomicBool::new(false));
    let was_evaluated_clone = Arc::clone(&was_evaluated);
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
    let was_evaluated_clone = Arc::clone(&was_evaluated);
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
            assert_eq!(*err.error(), "underlying error");
            assert_eq!(err.contexts(), ["Context evaluated: yes"].as_slice());
        },
        Ok(_) => panic!("expected error"),
    }
}

#[test]
fn test_with_context_and_accumulate() {
    let err = with_context("disk full", "save document");
    assert_eq!(*err.error(), "disk full");
    assert_eq!(err.contexts(), ["save document"].as_slice());

    let accumulated =
        accumulate_context("network timeout", ["attempt 1 failed", "attempt 2 failed"]);
    assert_eq!(*accumulated.error(), "network timeout");
    assert_eq!(
        accumulated.contexts(),
        ["attempt 2 failed", "attempt 1 failed"].as_slice()
    );
}

#[test]
fn test_context_error_map_error_and_from() {
    let err = ContextError::new(404).with_context("not found");
    let mapped = err.map_error(|code| format!("HTTP {code}"));
    assert_eq!(mapped.error(), "HTTP 404");
    assert_eq!(mapped.contexts(), ["not found"].as_slice());

    let from_err: ContextError<&str> = "raw error".into();
    assert_eq!(*from_err.error(), "raw error");
    assert!(from_err.contexts().is_empty());
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
fn test_context_error_contexts_slice() {
    let err = ContextError::new("core")
        .with_context("first")
        .with_context("second");

    assert_eq!(err.contexts(), ["second", "first"].as_slice());
}

#[test]
fn test_with_contexts_heterogeneous_and_ref_string() {
    let err = ContextError::new("core").with_contexts(["step 1", "step 2"]);
    assert_eq!(err.contexts(), ["step 2", "step 1"].as_slice());

    let owned = String::from("by ref");
    let err2 = err.with_context(&owned);
    assert_eq!(err2.contexts(), ["by ref", "step 2", "step 1"].as_slice());
}
