#![doc = include_str!("../../../docs/datatypes/operational.md")]

mod debug;
mod eval;
#[cfg(test)]
mod fixtures;
mod program;
mod teardown;

pub use program::Program;

use core::any::Any;
use core::convert::Infallible;

use alloc::boxed::Box;
use alloc::vec::Vec;

/// Domain command with an associated static output type.
pub trait Command: 'static {
    /// Return type produced by executing this command.
    type Output: 'static;

    /// Suspends this command into an infallible [`Program`].
    fn suspend<H: Handler<Self> + 'static>(self) -> Program<H, Self::Output>
    where
        Self: Sized,
    {
        Program::suspend(self)
    }

    /// Suspends this command into a fallible [`TryProgram`].
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
    fn try_handle(&mut self, cmd: C) -> Result<C::Output, Infallible> {
        Ok(self.handle(cmd))
    }
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
    // Ordered erased prefix steps followed by the typed tail.
    Then(Steps<H, E>, Box<TryProgram<H, A, E>>),
}

// Non-empty ordered prefix of erased steps; `head` runs first.
// `head` is boxed to keep `Node` sized; `rest` is a `Vec` so appending steps stays amortized.
struct Steps<H, E> {
    head: Box<TryProgram<H, AnyBox, E>>,
    rest: Vec<TryProgram<H, AnyBox, E>>,
}

impl<H, E> IntoIterator for Steps<H, E> {
    type Item = TryProgram<H, AnyBox, E>;
    type IntoIter =
        core::iter::Chain<core::iter::Once<Self::Item>, alloc::vec::IntoIter<Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        core::iter::once(*self.head).chain(self.rest)
    }
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
    const fn take_node(&mut self) -> Node<H, A, E> {
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
    pub const fn pure(val: A) -> Self {
        Self {
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
                let any_prog: TryProgram<H, AnyBox, E> = Self { node: Some(other) }.into_any();
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
    pub fn then<B: 'static>(mut self, next: TryProgram<H, B, E>) -> TryProgram<H, B, E> {
        match self.take_node() {
            Node::Pure(_) => next,
            node => {
                let mut previous = Self { node: Some(node) }.into_any();
                let steps = match previous.take_node() {
                    Node::Then(mut steps, tail) => {
                        steps.rest.push(*tail);
                        steps
                    },
                    node => Steps {
                        head: Box::new(TryProgram { node: Some(node) }),
                        rest: Vec::new(),
                    },
                };
                TryProgram {
                    node: Some(Node::Then(steps, Box::new(next))),
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

// Observable state inspection.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Returns `true` if the computation is a pure value.
    pub const fn is_pure(&self) -> bool {
        matches!(self.node, Some(Node::Pure(_)))
    }

    /// Returns `true` if the computation is a suspended command.
    pub const fn is_suspend(&self) -> bool {
        matches!(self.node, Some(Node::Suspend(_, _)))
    }

    /// Returns `true` if the computation is a sequenced continuation node.
    pub const fn is_bind(&self) -> bool {
        matches!(self.node, Some(Node::Bind(_, _) | Node::Then(_, _)))
    }
}

#[cfg(test)]
mod tests {
    use super::fixtures::*;
    use super::*;

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
}
