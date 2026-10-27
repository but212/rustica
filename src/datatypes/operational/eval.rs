use alloc::vec::Vec;

use super::{AnyBox, Node, Steps, TryContFn, TryProgram};

enum TryFrame<H, E> {
    Bind(TryContFn<H, E>),
    Then(TryProgram<H, AnyBox, E>),
}

// Trampoline interpreter.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Evaluates the program using `handler` with stack safety.
    ///
    /// # Errors
    ///
    /// Returns `Err(E)` if any suspended command fails in `handler`.
    ///
    /// # Panics
    ///
    /// Panics if static type erasure invariants are violated during downcasting.
    pub fn try_run(self, handler: &mut H) -> Result<A, E> {
        let mut cur: Node<H, AnyBox, E> = self.into_any().take_node();
        let mut stack: Vec<TryFrame<H, E>> = Vec::new();

        loop {
            let val = match cur {
                Node::Bind(mut sub, cont) => {
                    stack.push(TryFrame::Bind(cont));
                    cur = sub.take_node();
                    continue;
                },
                Node::Then(Steps { mut head, rest }, next) => {
                    stack.push(TryFrame::Then(*next));
                    for sub in rest.into_iter().rev() {
                        stack.push(TryFrame::Then(sub));
                    }
                    cur = head.take_node();
                    continue;
                },
                Node::Pure(val) => val,
                Node::Suspend(runner, cont) => cont(runner(handler)?),
            };

            match stack.pop() {
                Some(TryFrame::Bind(cont)) => {
                    cur = cont(val).take_node();
                },
                Some(TryFrame::Then(mut next)) => {
                    cur = next.take_node();
                },
                None => {
                    return Ok(*val
                        .downcast::<A>()
                        .expect("statically guaranteed final return type"));
                },
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::missing_panics_doc)]
mod tests {
    use alloc::string::{String, ToString};

    use super::*;
    use crate::datatypes::operational::fixtures::*;
    use crate::datatypes::operational::{Command, Program, TryHandler};

    #[test]
    fn test_right_associated_then_preserves_order() {
        let program = Add(10)
            .suspend()
            .then(Multiply(3).suspend().then(Fetch.suspend()));

        let mut interpreter = CalcInterpreter { current: 0 };
        assert_eq!(program.run(&mut interpreter), 30);
    }

    #[test]
    fn test_mixed_right_associated_then_and_then_preserves_order() {
        let program = Add(2).suspend().then(
            Fetch
                .suspend()
                .and_then(|value| Add(value).suspend())
                .then(Fetch.suspend()),
        );

        let mut interpreter = CalcInterpreter { current: 0 };
        assert_eq!(program.run(&mut interpreter), 4);
    }

    #[test]
    fn test_nested_then_chunks_flatten_in_order() {
        // Non-commutative commands: any reordering of flattened prefixes changes the result.
        let program = Add(1)
            .suspend()
            .then(Multiply(3).suspend())
            .then(Add(2).suspend().then(Multiply(5).suspend()))
            .then(Fetch.suspend());

        let mut interpreter = CalcInterpreter { current: 0 };
        assert_eq!(program.run(&mut interpreter), 25);
    }

    #[test]
    fn test_stack_safety_deep_chains() {
        // Unwinds 25,000 left-associated binds iteratively
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..25_000 {
            p = p.then(Add(1).suspend());
        }

        let mut interp = CalcInterpreter { current: 0 };
        p.run(&mut interp);
        assert_eq!(interp.current, 25_000);
    }

    #[test]
    fn test_deep_right_associated_chain_run_stack_safety() {
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..25_000 {
            p = Add(1).suspend().then(p);
        }

        let mut interp = CalcInterpreter { current: 0 };
        p.run(&mut interp);
        assert_eq!(interp.current, 25_000);
    }

    #[test]
    fn test_try_program_success_and_failure() {
        let program: TryProgram<FallibleCalc, i32, &'static str> =
            Add(15).try_suspend().then(Fetch.try_suspend());

        let mut success_interp = FallibleCalc {
            current: 5,
            should_fail: false,
            fetches: 0,
        };
        assert_eq!(program.try_run(&mut success_interp), Ok(20));
        assert_eq!(success_interp.fetches, 1);

        let failing_program: TryProgram<FallibleCalc, i32, &'static str> = Fetch
            .try_suspend()
            .then(Add(15).try_suspend())
            .then(Fetch.try_suspend());

        let mut fail_interp = FallibleCalc {
            current: 5,
            should_fail: true,
            fetches: 0,
        };
        assert_eq!(
            failing_program.try_run(&mut fail_interp),
            Err("overflow_simulated")
        );
        assert_eq!(fail_interp.fetches, 1);
    }

    #[test]
    fn test_rc_error_try_program() {
        use alloc::rc::Rc;

        struct FailCmd;
        impl Command for FailCmd {
            type Output = ();
        }

        struct FailHandler;
        impl TryHandler<FailCmd, Rc<String>> for FailHandler {
            fn try_handle(&mut self, _cmd: FailCmd) -> Result<(), Rc<String>> {
                Err(Rc::new("rc_err".to_string()))
            }
        }

        let prog: TryProgram<FailHandler, (), Rc<String>> = FailCmd.try_suspend();
        let mut handler = FailHandler;
        let res = prog.try_run(&mut handler);
        assert_eq!(res, Err(Rc::new("rc_err".to_string())));
    }
}
