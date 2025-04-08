use rustica::datatypes::cont;
use std::sync::Arc;

#[test]
fn test_cont_creation_and_run() {
    // Test pure creation and running
    let cont = cont::Cont::return_cont(42);
    let result = cont.run(|x| x * 2);
    assert_eq!(result, 84);

    // Test new creation and running
    let cont = cont::Cont::new(|k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| k(42));
    let result = cont.run(|x| x * 2);
    assert_eq!(result, 84);
}

#[test]
fn test_cont_functor() {
    // Test with reference version
    let cont = cont::Cont::return_cont(42);
    let mapped = cont.fmap(|x| x + 1);
    let result = mapped.run(|x| x * 2);
    assert_eq!(result, 86);
}

#[test]
fn test_cont_bind() {
    let cont = cont::Cont::return_cont(42);
    let bound = cont.bind(Arc::new(|x| cont::Cont::return_cont(x + 1)));
    let result = bound.run(|x| x * 2);
    assert_eq!(result, 86);
}

#[test]
fn test_cont_apply() {
    let cont_val = cont::Cont::return_cont(42);
    let cont_fn =
        cont::Cont::return_cont(Arc::new(|x: i32| x + 1) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    let applied = cont_val.apply(cont_fn);
    let result = applied.run(|x| x * 2);
    assert_eq!(result, 86);
}

#[test]
fn test_cont_complex_composition() {
    // Create a chain of computations
    let initial = cont::Cont::return_cont(10);
    let step1 = initial.fmap(|x| x * 2); // 20
    let step2 = step1.bind(Arc::new(|x| cont::Cont::return_cont(x + 5))); // 25
    let step3 = step2.fmap(|x| x - 3); // 22

    // Run the final computation
    let result = step3.run(|x| x);
    assert_eq!(result, 22);
}

#[test]
fn test_cont_error_handling() {
    // Simulate error handling with continuations
    let safe_div = |n: i32, d: i32| -> cont::Cont<String, i32> {
        if d == 0 {
            cont::Cont::new(|_: Arc<dyn Fn(i32) -> String + Send + Sync>| {
                "Division by zero".to_string()
            })
        } else {
            cont::Cont::return_cont(n / d)
        }
    };

    // Test successful case
    let result1 = safe_div(10, 2).run(|x| x.to_string());
    assert_eq!(result1, "5");

    // Test error case
    let result2 = safe_div(10, 0).run(|_| "Unexpected success".to_string());
    assert_eq!(result2, "Division by zero");
}

#[test]
fn test_cont_return_cont() {
    // Test Cont::return_cont
    let cont: cont::Cont<String, i32> = cont::Cont::return_cont(10);
    let result = cont.run(|x| format!("Result: {}", x));
    assert_eq!(result, "Result: 10");
}

#[test]
fn test_cont_call_cc() {
    // Test call_cc for early exit
    let computation_early_exit = cont::Cont::<String, i32>::return_cont(1).call_cc(|exit| {
        cont::Cont::return_cont(1).bind(Arc::new(move |x| {
            if x > 0 {
                // Exit early with value 100
                exit(100)
            } else {
                cont::Cont::return_cont(x + 1)
            }
        }))
    });
    let result_early = computation_early_exit.run(|x| x.to_string());
    assert_eq!(result_early, "100"); // Should exit early

    // Test call_cc without early exit
    let computation_no_exit = cont::Cont::<String, i32>::return_cont(5).call_cc(|_exit| {
        cont::Cont::return_cont(5).fmap(|x| x * 2) // 5 * 2 = 10
    });
    let result_no_exit = computation_no_exit.run(|x| x.to_string());
    assert_eq!(result_no_exit, "10");
}
