#![doc = include_str!("../../docs/datatypes/operational.md")]

use core::any::Any;
use core::convert::Infallible;
use core::fmt;

use alloc::boxed::Box;
use alloc::vec::Vec;

/// Domain command with an associated static output type.
pub trait Command: 'static {
    /// Return type produced by executing this command.
    type Output: 'static;

    /// Suspends this command into an infallible [`Program`].
    #[inline]
    fn suspend<H: Handler<Self> + 'static>(self) -> Program<H, Self::Output>
    where
        Self: Sized,
    {
        Program::suspend(self)
    }

    /// Suspends this command into a fallible [`TryProgram`].
    #[inline]
    fn try_suspend<H: TryHandler<Self, E> + 'static, E: 'static>(
        self,
    ) -> TryProgram<H, Self::Output, E>
    where
        Self: Sized,
    {
        TryProgram::suspend(self)
    }
}

/// Infallible handler for command `C`.
pub trait Handler<C: Command> {
    /// Interprets command `C`, producing its output.
    fn handle(&mut self, cmd: C) -> C::Output;
}

/// Fallible handler for command `C` with error type `E`.
pub trait TryHandler<C: Command, E> {
    /// Interprets command `C`, returning its output or an error of type `E`.
    fn try_handle(&mut self, cmd: C) -> Result<C::Output, E>;
}

// Infallible handlers automatically implement TryHandler with Infallible error.
impl<H: Handler<C>, C: Command> TryHandler<C, Infallible> for H {
    #[inline]
    fn try_handle(&mut self, cmd: C) -> Result<C::Output, Infallible> {
        Ok(self.handle(cmd))
    }
}

/// Suspends a command into an infallible [`Program`].
#[inline]
pub fn suspend<H: Handler<C> + 'static, C: Command>(cmd: C) -> Program<H, C::Output> {
    Program::suspend(cmd)
}

/// Suspends a command into a fallible [`TryProgram`].
#[inline]
pub fn try_suspend<H: TryHandler<C, E> + 'static, C: Command, E: 'static>(
    cmd: C,
) -> TryProgram<H, C::Output, E> {
    TryProgram::suspend(cmd)
}

// Internal type-erased step representation for trampoline evaluation.
type AnyBox = Box<dyn Any>;
type TryStepFn<H, E> = Box<dyn FnOnce(&mut H) -> Result<AnyBox, E>>;
type TryContFn<H, E> = Box<dyn FnOnce(AnyBox) -> TryProgram<H, AnyBox, E>>;

enum Node<H, A, E> {
    Pure(A),
    Suspend(TryStepFn<H, E>, Box<dyn FnOnce(AnyBox) -> A>),
    Bind(
        Box<TryProgram<H, AnyBox, E>>,
        Box<dyn FnOnce(AnyBox) -> TryProgram<H, A, E>>,
    ),
    // Ordered erased prefix steps followed by the typed tail; the prefix is always non-empty.
    Then(Vec<TryProgram<H, AnyBox, E>>, Box<TryProgram<H, A, E>>),
}

enum TryFrame<H, E> {
    Bind(TryContFn<H, E>),
    Then(TryProgram<H, AnyBox, E>),
}

/// Fallible Operational Monad computation with domain error `E`.
#[repr(transparent)]
pub struct TryProgram<H, A, E> {
    node: Option<Node<H, A, E>>,
}

impl<H, A, E> TryProgram<H, A, E> {
    /// Takes ownership of the node, leaving `None` transiently.
    ///
    /// Invariant: `node` is `Some` on all observable values; private ownership ensures unreachable panic.
    #[inline]
    fn take_node(&mut self) -> Node<H, A, E> {
        self.node.take().expect("TryProgram node already consumed")
    }
}

impl<H: 'static, E: 'static> TryProgram<H, (), E> {
    /// Suspends a command into a `TryProgram`.
    pub fn suspend<C>(cmd: C) -> TryProgram<H, C::Output, E>
    where
        C: Command,
        H: TryHandler<C, E>,
    {
        TryProgram {
            node: Some(Node::Suspend(
                Box::new(move |handler: &mut H| {
                    let out = handler.try_handle(cmd)?;
                    Ok(Box::new(out) as AnyBox)
                }),
                Box::new(|any_val: AnyBox| {
                    *any_val
                        .downcast::<C::Output>()
                        .expect("statically guaranteed command output type")
                }),
            )),
        }
    }
}

// Program construction and type erasure.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Wraps a pure value in a `TryProgram`.
    #[inline]
    pub const fn pure(val: A) -> Self {
        TryProgram {
            node: Some(Node::Pure(val)),
        }
    }

    /// Transforms the inner value with `f`.
    pub fn map<B: 'static, F>(self, f: F) -> TryProgram<H, B, E>
    where
        F: FnOnce(A) -> B + 'static,
    {
        self.and_then(move |a| TryProgram::pure(f(a)))
    }

    /// Sequences another computation from the result of `self`.
    pub fn and_then<B: 'static, F>(mut self, f: F) -> TryProgram<H, B, E>
    where
        F: FnOnce(A) -> TryProgram<H, B, E> + 'static,
    {
        match self.take_node() {
            Node::Pure(a) => f(a),
            other => {
                let any_prog: TryProgram<H, AnyBox, E> =
                    TryProgram { node: Some(other) }.into_any();
                TryProgram {
                    node: Some(Node::Bind(
                        Box::new(any_prog),
                        Box::new(move |any_val: AnyBox| {
                            let a = *any_val
                                .downcast::<A>()
                                .expect("statically guaranteed bind parameter type");
                            f(a)
                        }),
                    )),
                }
            },
        }
    }

    /// Sequences `next` after `self`, discarding `self`'s output.
    #[inline]
    pub fn then<B: 'static>(mut self, next: TryProgram<H, B, E>) -> TryProgram<H, B, E> {
        match self.take_node() {
            Node::Pure(_) => next,
            node => {
                let mut previous = TryProgram { node: Some(node) }.into_any();
                let previous_steps = match previous.take_node() {
                    Node::Then(mut steps, tail) => {
                        steps.push(*tail);
                        steps
                    },
                    node => alloc::vec![TryProgram { node: Some(node) }],
                };
                TryProgram {
                    node: Some(Node::Then(previous_steps, Box::new(next))),
                }
            },
        }
    }

    fn into_any(mut self) -> TryProgram<H, AnyBox, E> {
        let mut first_then_chunk = None;
        let mut remaining_then_chunks = Vec::new();
        let node = loop {
            match self.take_node() {
                Node::Then(subs, next) => {
                    if first_then_chunk.is_some() {
                        remaining_then_chunks.push(subs);
                    } else {
                        first_then_chunk = Some(subs);
                    }
                    self = *next;
                },
                node => break node,
            }
        };

        let mut erased = match node {
            Node::Pure(a) => TryProgram::pure(Box::new(a) as AnyBox),
            Node::Suspend(runner, cont) => TryProgram {
                node: Some(Node::Suspend(
                    runner,
                    Box::new(move |res| Box::new(cont(res)) as AnyBox),
                )),
            },
            Node::Bind(sub, cont) => TryProgram {
                node: Some(Node::Bind(sub, Box::new(move |res| cont(res).into_any()))),
            },
            Node::Then(_, _) => unreachable!("Then nodes are collected above"),
        };

        for subs in remaining_then_chunks.into_iter().rev() {
            erased = TryProgram {
                node: Some(Node::Then(subs, Box::new(erased))),
            };
        }
        if let Some(subs) = first_then_chunk {
            erased = TryProgram {
                node: Some(Node::Then(subs, Box::new(erased))),
            };
        }
        erased
    }
}

// Trampoline interpreter.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Evaluates the program using `handler` with stack safety.
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
                Node::Then(subs, next) => {
                    let mut subs = subs.into_iter();
                    let mut first = subs.next().expect("Then node has at least one step");
                    stack.push(TryFrame::Then(*next));
                    for sub in subs.rev() {
                        stack.push(TryFrame::Then(sub));
                    }
                    cur = first.take_node();
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

// Observable state inspection.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Returns `true` if the computation is a pure value.
    #[inline]
    pub const fn is_pure(&self) -> bool {
        matches!(self.node, Some(Node::Pure(_)))
    }

    /// Returns `true` if the computation is a suspended command.
    #[inline]
    pub const fn is_suspend(&self) -> bool {
        matches!(self.node, Some(Node::Suspend(_, _)))
    }

    /// Returns `true` if the computation is a sequenced continuation node.
    #[inline]
    pub const fn is_bind(&self) -> bool {
        matches!(self.node, Some(Node::Bind(_, _) | Node::Then(_, _)))
    }
}

// Iterative destruction.
fn drop_any_programs<H, E>(programs: impl IntoIterator<Item = TryProgram<H, AnyBox, E>>) {
    let mut pending = Vec::new();
    for mut program in programs {
        if let Some(node) = program.node.take() {
            pending.push(node);
        }
    }

    while let Some(node) = pending.pop() {
        match node {
            Node::Bind(mut sub, cont) => {
                if let Some(node) = sub.node.take() {
                    pending.push(node);
                }
                // Stack safety covers the explicit AST spine; captured closures may recurse on drop.
                drop(cont);
            },
            Node::Then(subs, mut next) => {
                for mut sub in subs {
                    if let Some(node) = sub.node.take() {
                        pending.push(node);
                    }
                }
                if let Some(node) = next.node.take() {
                    pending.push(node);
                }
            },
            Node::Pure(value) => drop(value),
            Node::Suspend(runner, cont) => drop((runner, cont)),
        }
    }
}

/// Iterative `Drop` implementation preventing stack overflows on deep un-evaluated chains.
///
/// Stack safety applies to explicit AST spines (`Then` and `Bind`), not closures capturing nested programs.
impl<H, A, E> Drop for TryProgram<H, A, E> {
    fn drop(&mut self) {
        let mut cur = self.node.take();
        while let Some(node) = cur {
            match node {
                Node::Then(subs, next) => {
                    drop_any_programs(subs);
                    let mut next = *next;
                    cur = next.node.take();
                },
                Node::Bind(sub, cont) => {
                    drop_any_programs([*sub]);
                    // Stack safety covers the explicit AST spine; captured closures may recurse on drop.
                    drop(cont);
                    return;
                },
                node => {
                    drop(node);
                    return;
                },
            }
        }
    }
}

/// Infallible Operational Monad computation.
///
/// Backed by [`TryProgram<H, A, Infallible>`].
#[repr(transparent)]
pub struct Program<H, A>(pub TryProgram<H, A, Infallible>);

impl<H: 'static> Program<H, ()> {
    /// Suspends a command into an infallible [`Program`].
    #[inline]
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
    #[inline]
    pub const fn pure(val: A) -> Self {
        Program(TryProgram::pure(val))
    }

    /// Transforms the inner value with `f`.
    #[inline]
    pub fn map<B: 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> B + 'static,
    {
        Program(self.0.map(f))
    }

    /// Sequences another computation from the result of `self`.
    #[inline]
    pub fn and_then<B: 'static, F>(self, f: F) -> Program<H, B>
    where
        F: FnOnce(A) -> Program<H, B> + 'static,
    {
        Program(self.0.and_then(move |a| f(a).0))
    }

    /// Sequences `next` after `self`, discarding `self`'s output.
    #[inline]
    pub fn then<B: 'static>(self, next: Program<H, B>) -> Program<H, B> {
        Program(self.0.then(next.0))
    }

    /// Evaluates the program using `handler` with stack safety.
    #[inline]
    pub fn run(self, handler: &mut H) -> A {
        match self.0.try_run(handler) {
            Ok(val) => val,
            Err(inf) => match inf {},
        }
    }

    /// Returns `true` if the computation is a pure value.
    #[inline]
    pub const fn is_pure(&self) -> bool {
        self.0.is_pure()
    }

    /// Returns `true` if the computation is a suspended command.
    #[inline]
    pub const fn is_suspend(&self) -> bool {
        self.0.is_suspend()
    }

    /// Returns `true` if the computation is a sequenced continuation node.
    #[inline]
    pub const fn is_bind(&self) -> bool {
        self.0.is_bind()
    }
}

impl<H, A: fmt::Debug> fmt::Debug for Program<H, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

// Non-recursive Debug implementation summarizing sub-computations without traversing children.
impl<H, A: fmt::Debug, E> fmt::Debug for TryProgram<H, A, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.node {
            Some(Node::Pure(a)) => f.debug_tuple("Pure").field(a).finish(),
            Some(Node::Suspend(_, _)) => f.debug_tuple("Suspend").field(&"<command>").finish(),
            Some(Node::Bind(_, _) | Node::Then(_, _)) => {
                f.debug_tuple("Bind").field(&"<sub-computation>").finish()
            },
            None => f.debug_tuple("Consumed").finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::{format, string::String};

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
            .and_then(|num| Add(num).suspend()) // 30 + 30 = 60
            .then(Stringify.suspend());

        let mut interpreter = CalcInterpreter { current: 0 };
        let output = program.run(&mut interpreter);
        assert_eq!(output, "Result: 60");
    }

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
    fn test_deep_chain_drop_stack_safety() {
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..50_000 {
            p = p.then(Add(1).suspend());
        }
        drop(p);
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
    fn test_deep_right_associated_chain_drop_stack_safety() {
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..50_000 {
            p = Add(1).suspend().then(p);
        }
        drop(p);
    }

    // Fallible tests
    struct FallibleCalc {
        current: i32,
        should_fail: bool,
        fetches: usize,
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
            self.fetches += 1;
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

        let bound_p = susp_p.and_then(|_| Program::pure(10));
        assert!(!bound_p.is_pure());
        assert!(!bound_p.is_suspend());
        assert!(bound_p.is_bind());
        assert_eq!(format!("{bound_p:?}"), "Bind(\"<sub-computation>\")");

        let and_then_p: Program<CalcInterpreter, i32> =
            Add(1).suspend().and_then(|_| Program::pure(10));
        assert!(and_then_p.is_bind());

        // TryProgram predicates
        let try_pure: TryProgram<FallibleCalc, i32, &str> = TryProgram::pure(99);
        assert!(try_pure.is_pure());
        assert!(!try_pure.is_suspend());
        assert!(!try_pure.is_bind());

        let try_susp: TryProgram<FallibleCalc, (), &str> = Add(1).try_suspend();
        assert!(try_susp.is_suspend());

        let try_bound = try_susp.and_then(|_| TryProgram::pure(100));
        assert!(try_bound.is_bind());

        let try_and_then: TryProgram<FallibleCalc, i32, &str> =
            Add(1).try_suspend().and_then(|_| TryProgram::pure(100));
        assert!(try_and_then.is_bind());
    }

    #[test]
    fn test_into_any_no_double_boxing() {
        let prog: Program<CalcInterpreter, i32> = Add(10)
            .suspend()
            .and_then(|_| Fetch.suspend())
            .and_then(|num| Program::pure(num * 2));

        let mut handler = CalcInterpreter { current: 5 };
        let res: i32 = prog.run(&mut handler);
        assert_eq!(res, 30); // (5 + 10) * 2
    }

    #[test]
    fn test_operational_miri_ownership_and_drop() {
        struct StrCmd(String);
        impl Command for StrCmd {
            type Output = String;
        }
        struct StrHandler;
        impl Handler<StrCmd> for StrHandler {
            fn handle(&mut self, cmd: StrCmd) -> String {
                format!("{}_handled", cmd.0)
            }
        }

        // 1. Program dropped without running
        let prog = StrCmd("first".to_string())
            .suspend::<StrHandler>()
            .and_then(|s| StrCmd(format!("{s}_second")).suspend())
            .and_then(|s| Program::pure(format!("{s}_done")));
        drop(prog);

        // 2. Program run to completion
        let prog2 = StrCmd("init".to_string())
            .suspend()
            .and_then(|s| Program::pure(format!("{s}_mid")))
            .and_then(|s| StrCmd(s).suspend());
        let mut h = StrHandler;
        let res = prog2.run(&mut h);
        assert_eq!(res, "init_handled_mid_handled");
    }

    #[test]
    fn test_anybox_pure_payload() {
        let val: Box<dyn Any> = Box::new(42_i32);
        let prog: Program<CalcInterpreter, Box<dyn Any>> = Program::pure(val);
        let mut calc = CalcInterpreter { current: 0 };
        let res = prog.run(&mut calc);
        assert_eq!(*res.downcast::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_anybox_command_output() {
        struct BoxCmd(i32);
        impl Command for BoxCmd {
            type Output = Box<dyn Any>;
        }
        struct BoxHandler;
        impl Handler<BoxCmd> for BoxHandler {
            fn handle(&mut self, cmd: BoxCmd) -> Box<dyn Any> {
                Box::new(cmd.0 * 2)
            }
        }
        let prog: Program<BoxHandler, Box<dyn Any>> = BoxCmd(21).suspend();
        let mut handler = BoxHandler;
        let res = prog.run(&mut handler);
        assert_eq!(*res.downcast::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_anybox_bind_transformation() {
        let prog: Program<CalcInterpreter, Box<dyn Any>> = Add(10)
            .suspend()
            .and_then(|_| Program::pure(Box::new(99_i32) as Box<dyn Any>));
        let mut calc = CalcInterpreter { current: 0 };
        let res = prog.run(&mut calc);
        assert_eq!(*res.downcast::<i32>().unwrap(), 99);
    }

    #[test]
    fn test_const_fn_capability() {
        const fn prog_flags<H: 'static, A: 'static>(p: &Program<H, A>) -> (bool, bool, bool) {
            (p.is_pure(), p.is_suspend(), p.is_bind())
        }
        const fn try_prog_flags<H: 'static, A: 'static, E: 'static>(
            p: &TryProgram<H, A, E>,
        ) -> (bool, bool, bool) {
            (p.is_pure(), p.is_suspend(), p.is_bind())
        }

        const fn make_prog() -> Program<CalcInterpreter, i32> {
            Program::pure(42)
        }
        const fn make_try_prog() -> TryProgram<FallibleCalc, i32, &'static str> {
            TryProgram::pure(42)
        }

        assert_eq!(prog_flags(&make_prog()), (true, false, false));
        assert_eq!(try_prog_flags(&make_try_prog()), (true, false, false));
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
