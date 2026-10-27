use alloc::{
    format,
    string::{String, ToString},
};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
enum TestCmd {
    Increment(i32),
    Fetch,
}

#[test]
fn test_pure_value() {
    let computation: Free<TestCmd, i32> = Free::pure(42);
    assert!(computation.is_pure());
    assert!(!computation.is_suspend());
    assert!(!computation.is_bind());
    assert_eq!(computation.as_pure(), Some(&42));
    assert_eq!(computation.to_pure(), Some(42));
}

#[test]
fn test_suspend_and_run() {
    let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
        .and_then(|_: ()| Free::<TestCmd, ()>::suspend(TestCmd::Increment(25)))
        .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    let mut counter = 0;
    let final_value: i32 = program.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            counter += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(counter) as AnyValue,
    });

    assert_eq!(final_value, 35);
}

#[test]
fn test_try_run_success_and_error() {
    let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
        .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    let mut counter = 0;
    let res: Result<i32, FreeError<()>> = program.try_run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            counter += n;
            Ok(Arc::new(()) as AnyValue)
        },
        TestCmd::Fetch => Ok(Arc::new(counter) as AnyValue),
    });
    assert_eq!(res, Ok(5));

    let failing_program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
        .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
    let err_res: Result<i32, FreeError<&'static str>> = failing_program.try_run(|cmd| match cmd {
        TestCmd::Increment(_) => Err("error during increment"),
        TestCmd::Fetch => Ok(Arc::new(0) as AnyValue),
    });
    assert_eq!(
        err_res,
        Err(FreeError::Interpreter("error during increment"))
    );

    let mismatch_program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5));
    let type_err: Result<(), FreeError<()>> =
        mismatch_program.try_run(|_| Ok(Arc::new(7_i64) as AnyValue));
    assert!(matches!(
        type_err,
        Err(FreeError::TypeMismatch { expected: "()" })
    ));
}

#[test]
fn test_runtime_type_mismatch_in_pipeline() {
    use core::sync::atomic::{AtomicU32, Ordering};
    let side_effect_count = Arc::new(AtomicU32::new(0));
    let count_clone = Arc::clone(&side_effect_count);

    // AST construction carries static types Free<TestCmd, ()> and Free<TestCmd, i32>
    let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
        .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    // Return String instead of expected i32
    let res: Result<i32, FreeError<()>> = program.try_run(move |cmd| match cmd {
        TestCmd::Increment(_) => {
            count_clone.fetch_add(1, Ordering::SeqCst);
            Ok(Arc::new(()) as AnyValue)
        },
        TestCmd::Fetch => Ok(Arc::new(String::from("wrong_type")) as AnyValue),
    });

    // First step executed side effect before failure
    assert_eq!(side_effect_count.load(Ordering::SeqCst), 1);
    // Downcast mismatch detected at runtime
    assert!(matches!(
        res,
        Err(FreeError::TypeMismatch { expected }) if expected == core::any::type_name::<i32>()
    ));
}

#[test]
#[should_panic(expected = "Free interpretation type mismatch: expected return type i32")]
fn test_run_panics_on_runtime_type_mismatch() {
    let program = Free::<TestCmd, i32>::suspend(TestCmd::Fetch);
    // Panics at runtime during downcast
    let _: i32 = program.run(|_| Arc::new("wrong_type") as AnyValue);
}

#[test]
fn test_apply_and_zip_with() {
    let func: Free<TestCmd, fn(i32) -> i32> = Free::pure(|x: i32| x + 10);
    let val: Free<TestCmd, i32> = Free::pure(5);
    let applied = func.apply(val);
    assert_eq!(applied.to_pure(), Some(15));

    let fa: Free<TestCmd, i32> = Free::pure(3);
    let fb: Free<TestCmd, i32> = Free::pure(4);
    let combined: Free<TestCmd, i32> = fa.zip_with(fb, |a, b| a * b);
    assert_eq!(combined.to_pure(), Some(12));

    let fa2: Free<TestCmd, i32> = Free::pure(3);
    let fb2: Free<TestCmd, i32> = Free::pure(4);
    let zipped = fa2.zip_with(fb2, |a, b| a + b);
    assert_eq!(zipped.to_pure(), Some(7));
}

#[test]
fn test_monad_laws() {
    // Left identity: pure(a).bind(f) == f(a)
    let a = 7;
    let f = |x: i32| Free::pure(x * 3);
    let left: Free<TestCmd, i32> = Free::pure(a).and_then(f);
    let right = f(a);
    assert_eq!(left.to_pure(), right.to_pure());

    let left_and_then: Free<TestCmd, i32> = Free::pure(a).and_then(f);
    assert_eq!(left_and_then.to_pure(), right.to_pure());

    // Right identity: m.bind(pure) == m
    let m: Free<TestCmd, i32> = Free::pure(42);
    let bound = m.and_then(Free::pure);
    assert_eq!(bound.to_pure(), Some(42));
    assert_eq!(m.and_then(Free::pure).to_pure(), Some(42));

    // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
    let g = |x: i32| Free::pure(x + 100);
    let m1: Free<TestCmd, i32> = Free::pure(5);
    let m2: Free<TestCmd, i32> = Free::pure(5);
    let r1 = m1.and_then(f).and_then(g);
    let r2 = m2.and_then(move |x| f(x).and_then(g));
    assert_eq!(r1.to_pure(), r2.to_pure());

    let r1_and_then = m1.and_then(f).and_then(g);
    let r2_and_then = m2.and_then(move |x| f(x).and_then(g));
    assert_eq!(r1_and_then.to_pure(), r2_and_then.to_pure());
}

#[test]
fn test_left_nested_stack_safety() {
    let mut p: Free<TestCmd, ()> = Free::pure(());
    for _ in 0..25_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }

    let mut count = 0;
    p.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            count += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(count) as AnyValue,
    });
    assert_eq!(count, 25_000);
}

#[test]
fn test_arc_clone_and_multiple_runs() {
    let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
        .then(Free::<TestCmd, ()>::suspend(TestCmd::Increment(20)))
        .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    // Run 1
    let mut c1 = 0;
    let r1: i32 = program.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c1 += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(c1) as AnyValue,
    });
    assert_eq!(r1, 30);

    // Run 2: same AST with different initial state
    let mut c2 = 100;
    let r2: i32 = program.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c2 += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(c2) as AnyValue,
    });
    assert_eq!(r2, 130);

    // Branch: clone AST and extend along two paths
    let branch_a = program.and_then(|total: i32| Free::pure(total * 2));
    let branch_b = program.and_then(|total: i32| Free::pure(total + 1000));

    let mut c_a = 0;
    let res_a: i32 = branch_a.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c_a += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(c_a) as AnyValue,
    });
    assert_eq!(res_a, 60); // 30 * 2

    let mut c_b = 0;
    let res_b: i32 = branch_b.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c_b += n;
            Arc::new(()) as AnyValue
        },
        TestCmd::Fetch => Arc::new(c_b) as AnyValue,
    });
    assert_eq!(res_b, 1030); // 30 + 1000
}

#[test]
fn test_debug_format() {
    let pure_val: Free<TestCmd, i32> = Free::pure(99);
    assert_eq!(format!("{pure_val:?}"), "Pure(99)");

    let bound: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    assert_eq!(
        format!("{bound:?}"),
        "Suspend(Increment(1), \"<continuation>\")"
    );
}

#[test]
fn test_debug_bind_spine_beyond_limit_reports_depth() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..25 {
        p = p.and_then(|_| Free::suspend(TestCmd::Increment(1)));
    }
    assert_eq!(format!("{p:?}"), "Bind(depth: 25, \"<continuation>\")");
}

#[test]
fn test_debug_right_then_spine_reports_depth() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..25 {
        p = Free::<TestCmd, ()>::suspend(TestCmd::Increment(1)).then(p);
    }
    assert_eq!(format!("{p:?}"), "Then(depth: 25)");
}

#[test]
fn test_debug_short_spines_render_nested() {
    let first: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));

    let bind: Free<TestCmd, ()> = first.and_then(|_| Free::suspend(TestCmd::Increment(2)));
    assert_eq!(
        format!("{bind:?}"),
        "Bind(Suspend(Increment(1), \"<continuation>\"), \"<continuation>\")"
    );

    let then: Free<TestCmd, ()> = first.then(Free::suspend(TestCmd::Increment(2)));
    assert_eq!(
        format!("{then:?}"),
        "Then(Suspend(Increment(1), \"<continuation>\"), Suspend(Increment(2), \"<continuation>\"))"
    );
}

#[test]
fn test_deep_debug_format_stack_safety() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..50_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    let debug_str = format!("{p:?}");
    assert!(debug_str.contains("depth: 50000"));
}

#[test]
fn test_deep_free_drop_with_clones() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..30_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    let q = p.clone();
    // Drop clone first, then original
    drop(q);
    drop(p);

    // Now drop original first, then clone
    let mut p2: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..30_000 {
        p2 = p2.then(Free::suspend(TestCmd::Increment(1)));
    }
    let q2 = p2.clone();
    drop(p2);
    drop(q2);
}

use core::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug)]
struct CloneCountingCmd {
    id: usize,
    clones: Arc<AtomicUsize>,
}

impl Clone for CloneCountingCmd {
    fn clone(&self) -> Self {
        self.clones.fetch_add(1, Ordering::SeqCst);
        Self {
            id: self.id,
            clones: Arc::clone(&self.clones),
        }
    }
}

#[test]
fn test_free_trampoline_unshared_bind_no_clone() {
    let counter = Arc::new(AtomicUsize::new(0));
    let cmd = CloneCountingCmd {
        id: 10,
        clones: Arc::clone(&counter),
    };

    // Chained Bind computation with 2 Bind layers
    let prog: Free<CloneCountingCmd, i32> = Free::suspend(cmd)
        .and_then(|n: i32| Free::pure(n + 1))
        .and_then(|n: i32| Free::pure(n * 2));

    counter.store(0, Ordering::SeqCst);

    let result = prog.run(|c| Arc::new(c.id as i32) as AnyValue);
    assert_eq!(result, 22);

    // Arc::try_unwrap moves unshared sub-computations without cloning;
    // cmd clones once during into_any().
    assert_eq!(counter.load(Ordering::SeqCst), 1);
}

#[test]
fn test_then_chain_run_phase_clones() {
    let counter = Arc::new(AtomicUsize::new(0));
    let cmd = CloneCountingCmd {
        id: 1,
        clones: Arc::clone(&counter),
    };

    let mut p: Free<CloneCountingCmd, usize> = Free::suspend(cmd.clone());
    for _ in 1..10 {
        p = p.then(Free::suspend(cmd.clone()));
    }

    // Reset counter before run to isolate run-phase clones
    counter.store(0, Ordering::SeqCst);
    let result: usize = p.run(|c| Arc::new(c.id) as AnyValue);
    assert_eq!(result, 1);

    // In a then-chain, each Suspend node clones once due to shared child Arcs.
    assert_eq!(counter.load(Ordering::SeqCst), 10);
}

#[test]
fn test_free_error() {
    let err: FreeError<&str> = FreeError::Interpreter("boom");
    assert!(err.is_interpreter());
    assert!(!err.is_type_mismatch());
    assert_eq!(err.to_string(), "Free interpreter error: boom");

    let mismatch: FreeError<&str> = FreeError::TypeMismatch { expected: "i32" };
    assert!(mismatch.is_type_mismatch());
    assert!(!mismatch.is_interpreter());
    assert_eq!(
        mismatch.to_string(),
        "Free interpretation type mismatch: expected return type i32"
    );
}

#[test]
fn test_anyvalue_pure_payload() {
    let val: AnyValue = Arc::new(42_i32);
    let prog: Free<TestCmd, AnyValue> = Free::pure(val);
    let res = prog.run(|_| Arc::new(()));
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn test_anyvalue_command_output() {
    let prog: Free<TestCmd, AnyValue> = Free::suspend(TestCmd::Fetch);
    let res = prog.run(|_| Arc::new(84_i32) as AnyValue);
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 84);
}

#[test]
fn test_anyvalue_suspend_with() {
    let val: AnyValue = Arc::new(42_i32);
    let prog: Free<TestCmd, AnyValue> =
        Free::suspend_with(TestCmd::Fetch, move |_| Arc::clone(&val));
    let res = prog.run(|_| Arc::new(()));
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn test_anyvalue_bind_transformation() {
    let prog: Free<TestCmd, AnyValue> = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
        .and_then(|_| Free::pure(Arc::new(99_i32) as AnyValue));
    let res = prog.run(|_| Arc::new(()) as AnyValue);
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 99);
}

#[test]
fn test_any_value_helper() {
    let val: AnyValue = any_value(42_i32);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);

    let unit_val: AnyValue = any_value(());
    assert!(unit_val.downcast_ref::<()>().is_some());
}

#[test]
fn test_then_semantic_equivalence() {
    use core::sync::atomic::{AtomicI32, Ordering};
    let p_then = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
        .then(Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
        .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    let p_bind = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
        .and_then(|_| Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
        .and_then(|_| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    let state_then = Arc::new(AtomicI32::new(0));
    let s_t = Arc::clone(&state_then);
    let res_then: i32 = p_then.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            s_t.fetch_add(n, Ordering::SeqCst);
            any_value(())
        },
        TestCmd::Fetch => any_value(s_t.load(Ordering::SeqCst)),
    });

    let state_bind = Arc::new(AtomicI32::new(0));
    let s_b = Arc::clone(&state_bind);
    let res_bind: i32 = p_bind.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            s_b.fetch_add(n, Ordering::SeqCst);
            any_value(())
        },
        TestCmd::Fetch => any_value(s_b.load(Ordering::SeqCst)),
    });

    assert_eq!(res_then, 15);
    assert_eq!(res_bind, 15);
    assert_eq!(
        state_then.load(Ordering::SeqCst),
        state_bind.load(Ordering::SeqCst)
    );
}

#[test]
fn test_then_is_then_not_bind() {
    let p1: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    let p2: Free<TestCmd, i32> = Free::suspend(TestCmd::Fetch);
    let chained = p1.then(p2);
    assert!(chained.is_then());
    assert!(!chained.is_bind());
    assert!(!chained.is_pure());
    assert!(!chained.is_suspend());
}

#[test]
fn test_then_pure_shortcircuit() {
    let p_pure = Free::<TestCmd, ()>::pure(());
    let p_suspend = Free::<TestCmd, i32>::suspend(TestCmd::Fetch);
    let chained = p_pure.then(p_suspend);
    assert!(chained.is_suspend());
    assert!(!chained.is_then());
    assert_eq!(chained.as_suspend(), Some(&TestCmd::Fetch));
}

#[test]
fn test_no_double_erasure_pure() {
    let val: AnyValue = any_value(42_i32);
    let prog: Free<TestCmd, AnyValue> = Free::pure(val);
    let erased: Free<TestCmd, AnyValue> = prog.into_any();
    let res = erased.run(|_| any_value(()));
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn test_no_double_erasure_then_chain() {
    let val: AnyValue = any_value(42_i32);
    let p1: Free<TestCmd, AnyValue> = Free::suspend(TestCmd::Fetch);
    let p2: Free<TestCmd, AnyValue> = Free::pure(val);
    let chain = p1.then(p2);
    let res = chain.run(|_| any_value(100_i32));
    assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn test_then_construction_linearity() {
    let counter = Arc::new(AtomicUsize::new(0));
    let cmd = CloneCountingCmd {
        id: 1,
        clones: Arc::clone(&counter),
    };

    // Measure n = 1000
    counter.store(0, Ordering::SeqCst);
    let mut p1000: Free<CloneCountingCmd, ()> = Free::suspend(cmd.clone());
    for _ in 0..1000 {
        p1000 = p1000.then(Free::<CloneCountingCmd, ()>::suspend(cmd.clone()));
    }
    let clones_1000 = counter.load(Ordering::SeqCst);

    // Measure n = 2000
    counter.store(0, Ordering::SeqCst);
    let mut p2000: Free<CloneCountingCmd, ()> = Free::suspend(cmd.clone());
    for _ in 0..2000 {
        p2000 = p2000.then(Free::<CloneCountingCmd, ()>::suspend(cmd.clone()));
    }
    let clones_2000 = counter.load(Ordering::SeqCst);

    let ratio = clones_2000 as f64 / clones_1000 as f64;
    assert!(
        (1.8..=2.2).contains(&ratio),
        "Expected linear scaling (~2.0), got ratio: {ratio}"
    );
}

#[test]
fn test_deep_then_drop() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..50_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    drop(p);
}

#[test]
fn test_mixed_bind_then_drop() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for i in 0..20_000 {
        if i % 2 == 0 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        } else {
            p = p.and_then(|_| Free::suspend(TestCmd::Increment(1)));
        }
    }
    drop(p);
}

#[test]
fn test_deep_then_debug() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..50_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    let debug_str = format!("{p:?}");
    assert!(debug_str.contains("Then(depth: 50000)"));
}

#[test]
fn test_deep_then_run() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..25_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    let mut count = 0;
    p.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            count += n;
            any_value(())
        },
        TestCmd::Fetch => any_value(count),
    });
    assert_eq!(count, 25_001);
}

#[test]
fn test_then_clone_reuse() {
    let prog = Free::<TestCmd, ()>::suspend(TestCmd::Increment(7))
        .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

    let prog_clone = prog.clone();

    let mut c1 = 0;
    let r1: i32 = prog.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c1 += n;
            any_value(())
        },
        TestCmd::Fetch => any_value(c1),
    });

    let mut c2 = 100;
    let r2: i32 = prog_clone.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c2 += n;
            any_value(())
        },
        TestCmd::Fetch => any_value(c2),
    });

    assert_eq!(r1, 7);
    assert_eq!(r2, 107);
}

#[test]
fn test_deep_then_drop_with_clones() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..30_000 {
        p = p.then(Free::suspend(TestCmd::Increment(1)));
    }
    let q = p.clone();
    drop(q);
    drop(p);

    let mut p2: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for _ in 0..30_000 {
        p2 = p2.then(Free::suspend(TestCmd::Increment(1)));
    }
    let q2 = p2.clone();
    drop(p2);
    drop(q2);
}

#[test]
fn test_accessors() {
    let p_pure: Free<TestCmd, i32> = Free::pure(42);
    assert!(p_pure.is_pure());
    assert_eq!(p_pure.as_pure(), Some(&42));
    assert_eq!(p_pure.as_suspend(), None);
    assert!(p_pure.as_then().is_none());

    let p_suspend: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(5));
    assert!(p_suspend.is_suspend());
    assert_eq!(p_suspend.as_suspend(), Some(&TestCmd::Increment(5)));
    assert_eq!(p_suspend.as_pure(), None);
    assert!(p_suspend.as_then().is_none());

    let p_then = p_suspend.then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
    assert!(p_then.is_then());
    assert!(p_then.as_then().is_some());
    assert_eq!(p_then.as_pure(), None);
    assert_eq!(p_then.as_suspend(), None);

    let p_bind = p_suspend.and_then(|_| Free::pure(10));
    assert!(p_bind.is_bind());
    assert_eq!(p_bind.as_pure(), None);
    assert_eq!(p_bind.as_suspend(), None);
    assert!(p_bind.as_then().is_none());
}

#[test]
fn test_monad_laws_effectful() {
    let mut trace1 = Vec::new();
    let f = |x: i32| {
        Free::<TestCmd, ()>::suspend(TestCmd::Increment(x)).and_then(move |_| Free::pure(x * 2))
    };

    // Left identity: pure(a).and_then(f) vs f(a)
    let left = Free::<TestCmd, i32>::pure(5).and_then(f);
    let right = f(5);

    let mut c1 = 0;
    let r_left = left.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c1 += n;
            trace1.push(format!("inc({n})"));
            any_value(())
        },
        TestCmd::Fetch => any_value(c1),
    });

    let mut trace2 = Vec::new();
    let mut c2 = 0;
    let r_right = right.run(|cmd| match cmd {
        TestCmd::Increment(n) => {
            c2 += n;
            trace2.push(format!("inc({n})"));
            any_value(())
        },
        TestCmd::Fetch => any_value(c2),
    });

    assert_eq!(r_left, r_right);
    assert_eq!(trace1, trace2);
}

#[test]
fn test_mixed_bind_then_debug() {
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    for i in 0..50_000 {
        p = if i % 2 == 0 {
            p.then(Free::suspend(TestCmd::Increment(1)))
        } else {
            p.and_then(|_| Free::suspend(TestCmd::Increment(1)))
        };
    }
    let debug_str = format!("{p:?}");
    assert!(!debug_str.is_empty());
}

#[test]
fn test_zigzag_then_debug() {
    let x: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
    let y: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(2));
    let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(0));
    for _ in 0..25_000 {
        p = x.clone().then(p).then(y.clone());
    }
    let debug_str = format!("{p:?}");
    assert!(!debug_str.is_empty());
}

#[test]
fn test_const_fn_accessors() {
    const fn inspect_pure(x: &Free<u8, u8>) -> bool {
        x.is_pure()
    }
    const fn inspect_suspend(x: &Free<u8, u8>) -> bool {
        x.is_suspend()
    }
    const fn inspect_bind(x: &Free<u8, u8>) -> bool {
        x.is_bind()
    }
    const fn inspect_then(x: &Free<u8, u8>) -> bool {
        x.is_then()
    }
    const fn inspect_as_pure(x: &Free<u8, u8>) -> Option<&u8> {
        x.as_pure()
    }
    const fn inspect_as_suspend(x: &Free<u8, u8>) -> Option<&u8> {
        x.as_suspend()
    }

    let p: Free<u8, u8> = Free::pure(42);
    assert!(inspect_pure(&p));
    assert!(!inspect_suspend(&p));
    assert!(!inspect_bind(&p));
    assert!(!inspect_then(&p));
    assert_eq!(inspect_as_pure(&p), Some(&42));
    assert_eq!(inspect_as_suspend(&p), None);
}
