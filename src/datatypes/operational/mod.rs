#![doc = include_str!("../../../docs/datatypes/operational.md")]

mod debug;
mod eval;
mod program;
mod teardown;
#[cfg(test)]
mod tests;

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

    #[inline]
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
