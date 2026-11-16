use core::convert::Infallible;

use super::TryProgram;

/// Infallible Operational Monad computation.
///
/// Alias of [`TryProgram<H, A, Infallible>`]; it shares every constructor and inspector of [`TryProgram`].
pub type Program<H, A> = TryProgram<H, A, Infallible>;

impl<H: 'static, A: 'static> TryProgram<H, A, Infallible> {
    /// Evaluates the program using `handler` with stack safety.
    pub fn run(self, handler: &mut H) -> A {
        match self.try_run(handler) {
            Ok(val) => val,
            Err(inf) => match inf {},
        }
    }
}

#[cfg(test)]
#[allow(clippy::missing_panics_doc)]
mod tests {
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::*;
    use crate::datatypes::operational::fixtures::*;
    use crate::datatypes::operational::{Command, Handler};

    #[test]
    fn test_statically_typed_pipeline() {
        // Test Command::suspend extension method and Program::suspend
        let program: Program<CalcInterpreter, String> = Add(10)
            .suspend()
            .then(Multiply(3).suspend())
            .then(Fetch.suspend())
            .and_then(|num| Add(num).suspend()) // 30 + 30 = 60
            .then(Stringify.suspend());

        let mut interpreter = CalcInterpreter { current: 0 };
        let output = program.run(&mut interpreter);
        assert_eq!(output, "Result: 60");
    }

    #[test]
    fn test_monad_laws() {
        type P = Program<CalcInterpreter, i32>;

        // Observable behavior = (result, final interpreter state); programs are consumed by `run`.
        fn observe(p: P) -> (i32, i32) {
            let mut interp = CalcInterpreter { current: 3 };
            let result = p.run(&mut interp);
            (result, interp.current)
        }

        let f = |x: i32| Add(x).suspend().and_then(move |()| P::pure(x * 2));
        let g = |x: i32| {
            Multiply(x + 1)
                .suspend()
                .and_then(move |()| P::pure(x + 100))
        };

        // Left identity: pure(a).and_then(f) == f(a)
        assert_eq!(observe(P::pure(5).and_then(f)), observe(f(5)));

        // Laws only relate two sides, so a defect that hits both sides alike (e.g. dropping
        // `g`) passes them; the expected (result, final state) of `m.and_then(f).and_then(g)`
        // is pinned too.
        #[allow(clippy::type_complexity)]
        let ms: [(&str, fn() -> P, (i32, i32)); 2] = [
            ("pure", || P::pure(5), (110, 88)),
            ("suspend", || Fetch.suspend(), (106, 42)),
        ];
        for (name, m, expected) in ms {
            assert_eq!(
                observe(m().and_then(f).and_then(g)),
                expected,
                "expected outcome: {name}"
            );

            // Right identity: m.and_then(pure) == m
            assert_eq!(
                observe(m().and_then(P::pure)),
                observe(m()),
                "right identity: {name}"
            );

            // Associativity: m.and_then(f).and_then(g) == m.and_then(|x| f(x).and_then(g))
            assert_eq!(
                observe(m().and_then(f).and_then(g)),
                observe(m().and_then(move |x| f(x).and_then(g))),
                "associativity: {name}"
            );
        }
    }

    #[test]
    fn test_rc_refcell_command_pipeline() {
        use alloc::rc::Rc;
        use core::cell::RefCell;

        struct LocalPushCmd(Rc<RefCell<Vec<i32>>>, i32);
        impl Command for LocalPushCmd {
            type Output = Rc<RefCell<Vec<i32>>>;
        }

        struct LocalHandler;
        impl Handler<LocalPushCmd> for LocalHandler {
            fn handle(&mut self, cmd: LocalPushCmd) -> Rc<RefCell<Vec<i32>>> {
                cmd.0.borrow_mut().push(cmd.1);
                cmd.0
            }
        }

        let shared = Rc::new(RefCell::new(vec![1]));
        let prog: Program<LocalHandler, Rc<RefCell<Vec<i32>>>> =
            LocalPushCmd(Rc::clone(&shared), 2)
                .suspend()
                .and_then(|rc| LocalPushCmd(rc, 3).suspend());

        let mut handler = LocalHandler;
        let result = prog.run(&mut handler);
        assert_eq!(*result.borrow(), vec![1, 2, 3]);
        assert_eq!(*shared.borrow(), vec![1, 2, 3]);
    }

    #[test]
    fn program_is_the_infallible_try_program() {
        fn run_infallible<H: 'static, A: 'static>(
            program: TryProgram<H, A, Infallible>, handler: &mut H,
        ) -> A {
            program.run(handler)
        }

        let program: Program<CalcInterpreter, i32> = Add(7).suspend().then(Fetch.suspend());
        let mut interpreter = CalcInterpreter { current: 0 };
        assert_eq!(run_infallible(program, &mut interpreter), 7);
    }
}
