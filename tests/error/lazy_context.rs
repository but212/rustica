use rustica::context;
use rustica::error::with_context_result;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn test_lazy_context_evaluation() {
    let was_evaluated = Arc::new(AtomicBool::new(false));
    let was_evaluated_clone = was_evaluated.clone();

    let result: Result<i32, &str> = Ok(42);
    
    // This should NOT evaluate the context because the result is Ok
    let _ = with_context_result(
        result,
        context!("This should not be evaluated: {}", {
            was_evaluated_clone.store(true, Ordering::SeqCst);
            "failed"
        })
    );

    assert!(!was_evaluated.load(Ordering::SeqCst), "Context was evaluated despite success!");
}

#[test]
fn test_lazy_context_evaluation_on_error() {
    let was_evaluated = Arc::new(AtomicBool::new(false));
    let was_evaluated_clone = was_evaluated.clone();

    let result: Result<i32, &str> = Err("oops");
    
    // This SHOULD evaluate the context because the result is Err
    let _ = with_context_result(
        result,
        context!("Context evaluated: {}", {
            was_evaluated_clone.store(true, Ordering::SeqCst);
            "yes"
        })
    );

    assert!(was_evaluated.load(Ordering::SeqCst), "Context was NOT evaluated on error!");
}
