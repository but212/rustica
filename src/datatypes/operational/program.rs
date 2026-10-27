use core::convert::Infallible;

use super::{Command, Handler, TryProgram};

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
