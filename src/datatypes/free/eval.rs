use alloc::sync::Arc;
use alloc::vec::Vec;

use super::{AnyValue, Free, FreeError, Node, downcast_any_value};

/// Continuation function for the [`Free`] trampoline.
type ContFn<F> = Arc<dyn Fn(AnyValue) -> Free<F, AnyValue> + Send + Sync + 'static>;

/// Evaluation frame for iterative trampoline execution.
enum Frame<F> {
    BindCont(ContFn<F>),
    ThenNext(Arc<Free<F, AnyValue>>),
}

fn unwrap_arc<T: Clone>(arc: Arc<T>) -> T {
    Arc::try_unwrap(arc).unwrap_or_else(|a| (*a).clone())
}

impl<F, A> Free<F, A> {
    /// Internal iterative trampoline evaluating both [`run`](Self::run) and [`try_run`](Self::try_run).
    ///
    /// # Errors
    ///
    /// Returns [`FreeError::Interpreter`] on interpreter failure, or [`FreeError::TypeMismatch`] on type mismatch.
    fn run_internal<Interp, E>(&self, mut interp: Interp) -> Result<A, FreeError<E>>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> Result<AnyValue, E>,
    {
        let mut cur: Node<F, AnyValue> = self.into_any().take_node();
        let mut stack: Vec<Frame<F>> = Vec::new();

        loop {
            match cur {
                Node::Bind(sub, cont) => {
                    stack.push(Frame::BindCont(cont));
                    cur = unwrap_arc(sub).take_node();
                },
                Node::Then(left, right) => {
                    stack.push(Frame::ThenNext(right));
                    cur = unwrap_arc(left).take_node();
                },
                Node::Pure(val) => match stack.pop() {
                    Some(Frame::BindCont(cont)) => {
                        cur = cont(val).take_node();
                    },
                    Some(Frame::ThenNext(next_comp)) => {
                        cur = unwrap_arc(next_comp).take_node();
                    },
                    None => {
                        return downcast_any_value::<A>(&val).ok_or(FreeError::TypeMismatch {
                            expected: core::any::type_name::<A>(),
                        });
                    },
                },
                Node::Suspend(cmd, cont) => {
                    let effect_res = interp(cmd).map_err(FreeError::Interpreter)?;
                    let any_box = cont(effect_res)
                        .map_err(|expected| FreeError::TypeMismatch { expected })?;
                    match stack.pop() {
                        Some(Frame::BindCont(next_cont)) => {
                            cur = next_cont(any_box).take_node();
                        },
                        Some(Frame::ThenNext(next_comp)) => {
                            cur = unwrap_arc(next_comp).take_node();
                        },
                        None => {
                            return downcast_any_value::<A>(&any_box).ok_or(
                                FreeError::TypeMismatch {
                                    expected: core::any::type_name::<A>(),
                                },
                            );
                        },
                    }
                },
            }
        }
    }

    /// Evaluates the computation using an effect interpreter.
    ///
    /// Evaluates chains iteratively, keeping call stack depth $O(1)$.
    ///
    /// # Panics
    ///
    /// Panics if the interpreter returns an [`AnyValue`] that does not match type `A`.
    /// Use [`try_run`](Self::try_run) to handle interpreter mismatches as a `Result`.
    pub fn run<Interp>(&self, mut interp: Interp) -> A
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> AnyValue,
    {
        match self.run_internal(|cmd| Ok::<_, core::convert::Infallible>(interp(cmd))) {
            Ok(val) => val,
            Err(FreeError::TypeMismatch { expected }) => {
                panic!("Free interpretation type mismatch: expected return type {expected}")
            },
            Err(FreeError::Interpreter(inf)) => match inf {},
        }
    }

    /// Evaluates the `Free` computation with a fallible effect interpreter.
    ///
    /// # Errors
    ///
    /// Returns `Err(FreeError::Interpreter(e))` on interpreter failure, or
    /// `Err(FreeError::TypeMismatch)` if the returned payload type does not match `A`.
    pub fn try_run<Interp, E>(&self, interp: Interp) -> Result<A, FreeError<E>>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> Result<AnyValue, E>,
    {
        self.run_internal(interp)
    }
}

#[cfg(test)]
#[allow(
    clippy::missing_panics_doc,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]
mod tests {
    use alloc::format;
    use alloc::string::String;
    use core::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    use crate::datatypes::free::any_value;
    use crate::datatypes::free::fixtures::*;

    #[test]
    fn test_suspend_and_run() {
        let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .and_then(|()| Free::<TestCmd, ()>::suspend(TestCmd::Increment(25)))
            .and_then(|()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .and_then(|(): ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .and_then(|(): ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
        let err_res: Result<i32, FreeError<&'static str>> =
            failing_program.try_run(|cmd| match cmd {
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
    fn test_then_semantic_equivalence() {
        use core::sync::atomic::{AtomicI32, Ordering};
        let p_then = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
            .then(Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
            .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        let p_bind = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
            .and_then(|()| Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
            .and_then(|()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
    fn test_monad_laws_effectful() {
        let mut trace1 = Vec::new();
        let f = |x: i32| {
            Free::<TestCmd, ()>::suspend(TestCmd::Increment(x))
                .and_then(move |()| Free::pure(x * 2))
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
}
