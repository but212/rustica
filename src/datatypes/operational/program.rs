use core::convert::Infallible;

use super::{Command, Handler, TryProgram};

/// Infallible Operational Monad computation.
///
/// Backed by [`TryProgram<H, A, Infallible>`].
#[repr(transparent)]
pub struct Program<H, A>(pub TryProgram<H, A, Infallible>);

impl<H: 'static> Program<H, ()> {
    /// Suspends a command into an infallible [`Program`].
    pub fn suspend<C>(cmd: C) -> Program<H, C::Output>
    where
        C: Command,
        H: Handler<C>,
    {
        Program(TryProgram::suspend(cmd))
    }
}

impl<H: 'static, A: 'static> Program<H, A> {
    /// Wraps a pure value in a [`Program`].
    pub const fn pure(val: A) -> Self {
        Self(TryProgram::pure(val))
    }

    /// Transforms the inner value with `f`.
    pub fn map<B: 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> B + 'static,
    {
        Program(self.0.map(f))
    }

    /// Sequences another computation from the result of `self`.
    pub fn and_then<B: 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> Program<H, B> + 'static,
    {
        Program(self.0.and_then(move |a| f(a).0))
    }

    /// Sequences `next` after `self`, discarding `self`'s output.
    pub fn then<B: 'static>(self, next: Program<H, B>) -> Program<H, B> {
        Program(self.0.then(next.0))
    }

    /// Evaluates the program using `handler` with stack safety.
    pub fn run(self, handler: &mut H) -> A {
        match self.0.try_run(handler) {
            Ok(val) => val,
            Err(inf) => match inf {},
        }
    }

    /// Returns `true` if the computation is a pure value.
    pub const fn is_pure(&self) -> bool {
        self.0.is_pure()
    }

    /// Returns `true` if the computation is a suspended command.
    pub const fn is_suspend(&self) -> bool {
        self.0.is_suspend()
    }

    /// Returns `true` if the computation is a sequenced continuation node.
    pub const fn is_bind(&self) -> bool {
        self.0.is_bind()
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::*;
    use crate::datatypes::operational::fixtures::*;

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
}
