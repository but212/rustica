//! # Operational Monad
//!
//! The `operational` module provides statically-typed operational monads ([`Program`] and [`TryProgram`]).
//!
//! Unlike dynamic Free monads that rely on untyped closures returning `AnyValue`, `Program` and
//! `TryProgram` bind each [`Command`] to its exact associated return type ([`Command::Output`]) at compile time.
//! An interpreter implements [`Handler<C>`] (or [`TryHandler<C, E>`]), guaranteeing that
//! returning an incorrect type is a **compile-time error**, making type mismatches unrepresentable.
//!
//! ## When to use `Free` vs `Program`
//!
//! - Use [`Free`](crate::datatypes::free::Free) when you need an **inspectable, reusable AST** (`Clone`)
//!   that can be transformed via natural transformations ([`fold_map`](crate::datatypes::free::Free::fold_map))
//!   or evaluated multiple times across different interpreters.
//! - Use [`Program`] / [`TryProgram`] when you need **zero-downcast, 100% compile-time type-safe execution**
//!   where each command's return type is statically enforced on the interpreter handler.
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::operational::{Command, Handler, Program};
//!
//! // 1. Define commands with their exact static output types
//! struct Add(i32);
//! impl Command for Add {
//!     type Output = ();
//! }
//!
//! struct Multiply(i32);
//! impl Command for Multiply {
//!     type Output = ();
//! }
//!
//! struct Get;
//! impl Command for Get {
//!     type Output = i32;
//! }
//!
//! // 2. Build a statically-typed program using Command::suspend or Program::suspend
//! let program = Add(5).suspend()
//!     .then(Multiply(3).suspend())
//!     .then(Get.suspend());
//!
//! // 3. Implement the interpreter handler
//! struct Calculator {
//!     current: i32,
//! }
//!
//! impl Handler<Add> for Calculator {
//!     fn handle(&mut self, cmd: Add) {
//!         self.current += cmd.0;
//!     }
//! }
//!
//! impl Handler<Multiply> for Calculator {
//!     fn handle(&mut self, cmd: Multiply) {
//!         self.current *= cmd.0;
//!     }
//! }
//!
//! impl Handler<Get> for Calculator {
//!     fn handle(&mut self, _cmd: Get) -> i32 {
//!         self.current
//!     }
//! }
//!
//! // 4. Run the program with complete stack safety and static type checking
//! let mut calc = Calculator { current: 0 };
//! let result = program.run(&mut calc);
//! assert_eq!(result, 15);
//! ```

use std::any::Any;
use std::convert::Infallible;
use std::fmt;

/// A domain command with an associated static output type.
pub trait Command: Send + Sync + 'static {
    /// The exact return type produced by executing this command.
    type Output: Send + Sync + 'static;

    /// Suspends this command into a statically-typed infallible [`Program`].
    #[inline]
    fn suspend<H: Handler<Self> + 'static>(self) -> Program<H, Self::Output>
    where
        Self: Sized,
    {
        Program::suspend(self)
    }

    /// Suspends this command into a statically-typed fallible [`TryProgram`].
    #[inline]
    fn try_suspend<H: TryHandler<Self, E> + 'static, E: Send + Sync + 'static>(
        self,
    ) -> TryProgram<H, Self::Output, E>
    where
        Self: Sized,
    {
        TryProgram::suspend(self)
    }
}

/// An infallible handler for a specific command `C`.
pub trait Handler<C: Command> {
    /// Interprets command `C`, producing its statically-typed output.
    fn handle(&mut self, cmd: C) -> C::Output;
}

/// A fallible handler for a specific command `C` with error type `E`.
pub trait TryHandler<C: Command, E> {
    /// Interprets command `C`, returning either its output or an error of type `E`.
    fn try_handle(&mut self, cmd: C) -> Result<C::Output, E>;
}

// Infallible handlers automatically implement TryHandler with Infallible error
impl<H: Handler<C>, C: Command> TryHandler<C, Infallible> for H {
    #[inline]
    fn try_handle(&mut self, cmd: C) -> Result<C::Output, Infallible> {
        Ok(self.handle(cmd))
    }
}

/// Standalone helper to suspend a command into an infallible [`Program`].
#[inline]
pub fn suspend<H: Handler<C> + 'static, C: Command>(cmd: C) -> Program<H, C::Output> {
    Program::suspend(cmd)
}

/// Standalone helper to suspend a command into a fallible [`TryProgram`].
#[inline]
pub fn try_suspend<H: TryHandler<C, E> + 'static, C: Command, E: Send + Sync + 'static>(
    cmd: C,
) -> TryProgram<H, C::Output, E> {
    TryProgram::suspend(cmd)
}

// Internal type-erased step representation for trampoline evaluation
type AnyBox = Box<dyn Any + Send + Sync>;
type TryStepFn<H, E> = Box<dyn FnOnce(&mut H) -> Result<AnyBox, E> + Send + Sync>;
type TryContFn<H, E> = Box<dyn FnOnce(AnyBox) -> TryProgram<H, AnyBox, E> + Send + Sync>;

enum Node<H, A, E> {
    Pure(A),
    Suspend(TryStepFn<H, E>, Box<dyn FnOnce(AnyBox) -> A + Send + Sync>),
    Bind(
        Box<TryProgram<H, AnyBox, E>>,
        Box<dyn FnOnce(AnyBox) -> TryProgram<H, A, E> + Send + Sync>,
    ),
    Done,
}

/// Core statically-typed fallible Operational Monad computation with domain error `E`.
pub struct TryProgram<H, A, E> {
    node: Node<H, A, E>,
}

impl<H, A, E> TryProgram<H, A, E> {
    #[inline]
    fn take_node(&mut self) -> Node<H, A, E> {
        std::mem::replace(&mut self.node, Node::Done)
    }
}

impl<H: 'static, E: Send + Sync + 'static> TryProgram<H, (), E> {
    /// Suspends a statically-typed command into a `TryProgram`.
    pub fn suspend<C>(cmd: C) -> TryProgram<H, C::Output, E>
    where
        C: Command,
        H: TryHandler<C, E>,
    {
        TryProgram {
            node: Node::Suspend(
                Box::new(move |handler: &mut H| {
                    let out = handler.try_handle(cmd)?;
                    Ok(Box::new(out) as AnyBox)
                }),
                Box::new(|any_val: AnyBox| {
                    *any_val
                        .downcast::<C::Output>()
                        .expect("statically guaranteed command output type")
                }),
            ),
        }
    }
}

impl<H: 'static, A: Send + Sync + 'static, E: Send + Sync + 'static> TryProgram<H, A, E> {
    /// Wraps a pure value in a `TryProgram`.
    #[inline]
    pub fn pure(val: A) -> Self {
        TryProgram {
            node: Node::Pure(val),
        }
    }

    /// Transforms the inner value using a pure function.
    pub fn fmap<B: Send + Sync + 'static, F>(self, f: F) -> TryProgram<H, B, E>
    where
        F: FnOnce(A) -> B + Send + Sync + 'static,
    {
        self.bind(move |a| TryProgram::pure(f(a)))
    }

    /// Sequences another fallible computation from the result of this one.
    pub fn bind<B: Send + Sync + 'static, F>(mut self, f: F) -> TryProgram<H, B, E>
    where
        F: FnOnce(A) -> TryProgram<H, B, E> + Send + Sync + 'static,
    {
        match self.take_node() {
            Node::Pure(a) => f(a),
            other => {
                let any_prog: TryProgram<H, AnyBox, E> = TryProgram { node: other }.into_any();
                TryProgram {
                    node: Node::Bind(
                        Box::new(any_prog),
                        Box::new(move |any_val: AnyBox| {
                            let a = *any_val
                                .downcast::<A>()
                                .expect("statically guaranteed bind parameter type");
                            f(a)
                        }),
                    ),
                }
            },
        }
    }

    /// Sequences another computation, ignoring the output of the current one.
    #[inline]
    pub fn then<B: Send + Sync + 'static>(self, next: TryProgram<H, B, E>) -> TryProgram<H, B, E> {
        self.bind(move |_| next)
    }

    fn into_any(mut self) -> TryProgram<H, AnyBox, E> {
        match self.take_node() {
            Node::Pure(a) => TryProgram::pure(Box::new(a) as AnyBox),
            Node::Suspend(runner, cont) => TryProgram {
                node: Node::Suspend(runner, Box::new(move |res| Box::new(cont(res)) as AnyBox)),
            },
            Node::Bind(sub, cont) => TryProgram {
                node: Node::Bind(sub, Box::new(move |res| cont(res).into_any())),
            },
            Node::Done => TryProgram { node: Node::Done },
        }
    }

    /// Evaluates the fallible program to completion with stack safety using the provided handler.
    pub fn try_run(self, handler: &mut H) -> Result<A, E> {
        let mut cur: TryProgram<H, AnyBox, E> = self.into_any();
        let mut stack: Vec<TryContFn<H, E>> = Vec::new();

        loop {
            match cur.take_node() {
                Node::Bind(sub, cont) => {
                    stack.push(cont);
                    cur = *sub;
                },
                Node::Pure(val) => match stack.pop() {
                    Some(cont) => {
                        cur = cont(val);
                    },
                    None => {
                        return Ok(*val
                            .downcast::<A>()
                            .expect("statically guaranteed final return type"));
                    },
                },
                Node::Suspend(runner, cont) => {
                    let res = runner(handler)?;
                    let val = cont(res);
                    match stack.pop() {
                        Some(next_cont) => {
                            cur = next_cont(val);
                        },
                        None => {
                            return Ok(*val
                                .downcast::<A>()
                                .expect("statically guaranteed final return type"));
                        },
                    }
                },
                Node::Done => unreachable!("TryProgram node consumed prematurely"),
            }
        }
    }

    /// Returns `true` if the program is a pure value.
    #[inline]
    pub fn is_pure(&self) -> bool {
        matches!(self.node, Node::Pure(_))
    }

    /// Returns `true` if the program is a suspended command.
    #[inline]
    pub fn is_suspend(&self) -> bool {
        matches!(self.node, Node::Suspend(_, _))
    }

    /// Returns `true` if the program is a sequenced bind node.
    #[inline]
    pub fn is_bind(&self) -> bool {
        matches!(self.node, Node::Bind(_, _))
    }
}

/// Custom iterative Drop implementation to prevent stack overflows on deep un-evaluated chains.
impl<H, A, E> Drop for TryProgram<H, A, E> {
    fn drop(&mut self) {
        if let Node::Bind(ref mut sub, _) = self.node {
            let mut cur = std::mem::replace(sub, Box::new(TryProgram { node: Node::Done }));
            while let Node::Bind(ref mut next, _) = cur.node {
                cur = std::mem::replace(next, Box::new(TryProgram { node: Node::Done }));
            }
        }
    }
}

/// A statically-typed infallible Operational Monad computation.
///
/// Backed by [`TryProgram<H, A, Infallible>`], providing a zero-cost infallible API.
#[repr(transparent)]
pub struct Program<H, A>(pub TryProgram<H, A, Infallible>);

impl<H: 'static> Program<H, ()> {
    /// Suspends a statically-typed command into an infallible [`Program`].
    #[inline]
    pub fn suspend<C>(cmd: C) -> Program<H, C::Output>
    where
        C: Command,
        H: Handler<C>,
    {
        Program(TryProgram::suspend(cmd))
    }
}

impl<H: 'static, A: Send + Sync + 'static> Program<H, A> {
    /// Wraps a pure value in a [`Program`].
    #[inline]
    pub fn pure(val: A) -> Self {
        Program(TryProgram::pure(val))
    }

    /// Transforms the inner value using a pure function.
    #[inline]
    pub fn fmap<B: Send + Sync + 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> B + Send + Sync + 'static,
    {
        Program(self.0.fmap(f))
    }

    /// Sequences another computation from the result of this one.
    #[inline]
    pub fn bind<B: Send + Sync + 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> Program<H, B> + Send + Sync + 'static,
    {
        Program(self.0.bind(move |a| f(a).0))
    }

    /// Sequences another computation, ignoring the output of the current one.
    #[inline]
    pub fn then<B: Send + Sync + 'static>(self, next: Program<H, B>) -> Program<H, B> {
        self.bind(move |_| next)
    }

    /// Evaluates the program to completion with stack safety using the provided handler.
    #[inline]
    pub fn run(self, handler: &mut H) -> A {
        match self.0.try_run(handler) {
            Ok(val) => val,
            Err(inf) => match inf {},
        }
    }

    /// Returns `true` if the program is a pure value.
    #[inline]
    pub fn is_pure(&self) -> bool {
        self.0.is_pure()
    }

    /// Returns `true` if the program is a suspended command.
    #[inline]
    pub fn is_suspend(&self) -> bool {
        self.0.is_suspend()
    }

    /// Returns `true` if the program is a sequenced bind node.
    #[inline]
    pub fn is_bind(&self) -> bool {
        self.0.is_bind()
    }
}

impl<H, A: fmt::Debug> fmt::Debug for Program<H, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<H, A: fmt::Debug, E> fmt::Debug for TryProgram<H, A, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.node {
            Node::Pure(a) => f.debug_tuple("Pure").field(a).finish(),
            Node::Suspend(_, _) => f.debug_tuple("Suspend").field(&"<command>").finish(),
            Node::Bind(_, _) => f.debug_tuple("Bind").field(&"<sub-computation>").finish(),
            Node::Done => f.debug_tuple("Done").finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Add(i32);
    impl Command for Add {
        type Output = ();
    }

    struct Multiply(i32);
    impl Command for Multiply {
        type Output = ();
    }

    struct Fetch;
    impl Command for Fetch {
        type Output = i32;
    }

    struct Stringify;
    impl Command for Stringify {
        type Output = String;
    }

    struct CalcInterpreter {
        current: i32,
    }

    impl Handler<Add> for CalcInterpreter {
        fn handle(&mut self, cmd: Add) {
            self.current += cmd.0;
        }
    }

    impl Handler<Multiply> for CalcInterpreter {
        fn handle(&mut self, cmd: Multiply) {
            self.current *= cmd.0;
        }
    }

    impl Handler<Fetch> for CalcInterpreter {
        fn handle(&mut self, _cmd: Fetch) -> i32 {
            self.current
        }
    }

    impl Handler<Stringify> for CalcInterpreter {
        fn handle(&mut self, _cmd: Stringify) -> String {
            format!("Result: {}", self.current)
        }
    }

    #[test]
    fn test_statically_typed_pipeline() {
        // Test Command::suspend extension method and Program::suspend
        let program: Program<CalcInterpreter, String> = Add(10)
            .suspend()
            .then(Multiply(3).suspend())
            .then(Fetch.suspend())
            .bind(|num| Add(num).suspend()) // 30 + 30 = 60
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
        let left = Program::<CalcInterpreter, i32>::pure(a).bind(f);
        let mut interp = CalcInterpreter { current: 0 };
        assert_eq!(left.run(&mut interp), 84);

        // Right identity: m.bind(pure) == m
        let m = Program::<CalcInterpreter, i32>::pure(100);
        let right = m.bind(Program::pure);
        assert_eq!(right.run(&mut interp), 100);
    }

    #[test]
    fn test_stack_safety_deep_chains() {
        // Unwinds 25,000 left-associated binds iteratively without call-stack overflow
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..25_000 {
            p = p.then(Add(1).suspend());
        }

        let mut interp = CalcInterpreter { current: 0 };
        p.run(&mut interp);
        assert_eq!(interp.current, 25_000);
    }

    #[test]
    fn test_deep_chain_drop_stack_safety() {
        // Critical verification for Finding 1 [P1]:
        // Dropping a 50,000-deep un-evaluated left-associated chain must NOT cause a stack overflow!
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..50_000 {
            p = p.then(Add(1).suspend());
        }
        // Explicit drop to verify iterative Drop safety
        drop(p);
    }

    // Fallible tests
    struct FallibleCalc {
        current: i32,
        should_fail: bool,
    }

    impl TryHandler<Add, &'static str> for FallibleCalc {
        fn try_handle(&mut self, cmd: Add) -> Result<(), &'static str> {
            if self.should_fail {
                Err("overflow_simulated")
            } else {
                self.current += cmd.0;
                Ok(())
            }
        }
    }

    impl TryHandler<Fetch, &'static str> for FallibleCalc {
        fn try_handle(&mut self, _cmd: Fetch) -> Result<i32, &'static str> {
            Ok(self.current)
        }
    }

    #[test]
    fn test_try_program_success_and_failure() {
        let program: TryProgram<FallibleCalc, i32, &'static str> =
            Add(15).try_suspend().then(Fetch.try_suspend());

        let mut success_interp = FallibleCalc {
            current: 5,
            should_fail: false,
        };
        assert_eq!(program.try_run(&mut success_interp), Ok(20));

        let failing_program: TryProgram<FallibleCalc, i32, &'static str> =
            Add(15).try_suspend().then(Fetch.try_suspend());

        let mut fail_interp = FallibleCalc {
            current: 5,
            should_fail: true,
        };
        assert_eq!(
            failing_program.try_run(&mut fail_interp),
            Err("overflow_simulated")
        );
    }

    #[test]
    fn test_predicates_and_debug() {
        let pure_p: Program<CalcInterpreter, i32> = Program::pure(42);
        assert!(pure_p.is_pure());
        assert!(!pure_p.is_suspend());
        assert!(!pure_p.is_bind());
        assert_eq!(format!("{pure_p:?}"), "Pure(42)");

        let susp_p: Program<CalcInterpreter, ()> = Add(1).suspend();
        assert!(!susp_p.is_pure());
        assert!(susp_p.is_suspend());
        assert!(!susp_p.is_bind());
        assert_eq!(format!("{susp_p:?}"), "Suspend(\"<command>\")");

        let bound_p = susp_p.bind(|_| Program::pure(10));
        assert!(!bound_p.is_pure());
        assert!(!bound_p.is_suspend());
        assert!(bound_p.is_bind());
        assert_eq!(format!("{bound_p:?}"), "Bind(\"<sub-computation>\")");

        // TryProgram predicates
        let try_pure: TryProgram<FallibleCalc, i32, &str> = TryProgram::pure(99);
        assert!(try_pure.is_pure());
        assert!(!try_pure.is_suspend());
        assert!(!try_pure.is_bind());

        let try_susp: TryProgram<FallibleCalc, (), &str> = Add(1).try_suspend();
        assert!(try_susp.is_suspend());

        let try_bound = try_susp.bind(|_| TryProgram::pure(100));
        assert!(try_bound.is_bind());
    }
}
