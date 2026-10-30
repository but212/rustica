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
        // Left identity: pure(a).bind(f) == f(a)
        let a = 42;
        let f = |x: i32| Program::<CalcInterpreter, i32>::pure(x * 2);
        let left = Program::<CalcInterpreter, i32>::pure(a).and_then(f);
        let mut interp = CalcInterpreter { current: 0 };
        assert_eq!(left.run(&mut interp), 84);

        // Right identity: m.bind(pure) == m
        let m = Program::<CalcInterpreter, i32>::pure(100);
        let right = m.and_then(Program::pure);
        assert_eq!(right.run(&mut interp), 100);

        let m2 = Program::<CalcInterpreter, i32>::pure(100);
        assert_eq!(m2.and_then(Program::pure).run(&mut interp), 100);
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
