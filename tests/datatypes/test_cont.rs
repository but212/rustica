use rustica::datatypes::cont;
use std::sync::Arc;

#[test]
fn test_cont_monadic_fundamentals() {
    // 1. Pure creation and running (return_cont)
    let c = cont::Cont::return_cont(42);
    assert_eq!(c.run(|x| x), 42);

    // 2. Functor (fmap)
    let mapped = c.clone().fmap(|x| x * 2);
    assert_eq!(mapped.run(|x| x), 84);

    // 3. Monad (bind)
    let bound = c.clone().bind(|x| cont::Cont::return_cont(x + 8));
    assert_eq!(bound.run(|x| x), 50);

    // 4. Applicative (apply)
    let f =
        cont::Cont::return_cont(Arc::new(|x: i32| x - 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    let applied = c.apply(f);
    assert_eq!(applied.run(|x| x), 40);
}

#[test]
fn test_cont_control_flow() {
    // 1. call_cc early exit: Jump out of the computation via the exit continuation
    let computation = cont::Cont::<String, i32>::return_cont(1).call_cc(|exit| {
        cont::Cont::return_cont(1).bind(move |x| {
            if x > 0 {
                exit(100) // Jump directly to the final continuation
            } else {
                cont::Cont::return_cont(x + 1)
            }
        })
    });
    assert_eq!(computation.run(|x| x.to_string()), "100");

    // 2. call_cc normal path: Continues normally if exit is not called
    let normal = cont::Cont::<i32, i32>::return_cont(5)
        .call_cc(|_| cont::Cont::return_cont(5).fmap(|x| x * 2));
    assert_eq!(normal.run(|x| x), 10);

    // 3. Non-local exit pattern for simulated error handling
    let safe_div = |n: i32, d: i32| -> cont::Cont<String, i32> {
        if d == 0 {
            cont::Cont::new(|_| "Error: DivByZero".to_string())
        } else {
            cont::Cont::return_cont(n / d)
        }
    };
    assert_eq!(safe_div(10, 2).run(|x| x.to_string()), "5");
    assert_eq!(
        safe_div(10, 0).run(|_| "Success".to_string()),
        "Error: DivByZero"
    );
}

#[test]
fn test_cont_chaining_and_laws() {
    let c = cont::Cont::return_cont(10);

    // 1. Complex chaining of multiple steps
    let chain = c
        .clone()
        .fmap(|x| x * 2) // 20
        .bind(|x| cont::Cont::return_cont(x + 5)) // 25
        .fmap(|x| x - 3); // 22
    assert_eq!(chain.run(|x| x), 22);

    // 2. Monad Identity Laws
    assert_eq!(
        c.clone().bind(cont::Cont::return_cont).run(|x| x),
        c.run(|x| x)
    );
}
