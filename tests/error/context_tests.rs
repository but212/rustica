
use rustica::error::ErrorPipeline;

#[test]
fn test_context_dropped_on_success() {
    let result = ErrorPipeline::new(Ok(1))
        .with_context("context 1") // Should be dropped
        .and_then(|_| Err::<(), &str>("error"))
        .finish();
    
    match result {
        Ok(_) => panic!("Expected error"),
        Err(e) => {
            let contexts = e.context();
            assert_eq!(contexts.len(), 0, "Context should be dropped if pipeline was Ok when added");
        }
    }
}

#[test]
fn test_context_preserved_on_failure() {
        let result = ErrorPipeline::new(Err::<(), &str>("original error"))
        .with_context("context 1")
        .finish();

    match result {
        Ok(_) => panic!("Expected error"),
        Err(e) => {
            let contexts = e.context();
            assert_eq!(contexts.len(), 1);
            assert_eq!(contexts[0], "context 1");
        }
    }
}

#[test]
fn test_context_accumulation_logic() {
    // Ok -> with_context(A) -> Err -> with_context(B)
    // A should be dropped, B should be kept.
    let result = ErrorPipeline::new(Ok(1))
        .with_context("context A")
        .and_then(|_| Err::<(), &str>("error"))
        .with_context("context B")
        .finish();
    
    match result {
        Ok(_) => panic!("Expected error"),
        Err(e) => {
            let contexts = e.context();
            assert_eq!(contexts.len(), 1);
            assert_eq!(contexts[0], "context B");
        }
    }
}
