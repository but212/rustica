//! # Free Monad
//!
//! `Free<F, A>` represents a computation as a tree of commands `F`, separating the program
//! definition from its execution.
//!
//! ## Execution and Stack Safety
//!
//! - **Evaluation**: Evaluated with [`run`](Free::run) or [`try_run`](Free::try_run). An internal
//!   heap stack unwinds left-associated chains (`a.then(b).then(c)`), keeping call stack frames $O(1)$.
//! - **Error handling**: [`try_run`](Free::try_run) returns [`FreeError`] on interpreter error or
//!   downcast mismatch instead of panicking.
//! - **Drop and Debug**: Traverses nested chains iteratively to prevent stack overflows when
//!   dropping or formatting large programs.
//! - **Reuse**: Backed by `Arc`, allowing programs to be cloned and evaluated multiple times.
//! - **IO conversion**: [`fold_map`](Free::fold_map) converts the program into a lazy [`IO`].
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::free::{AnyValue, Free};
//! use std::sync::Arc;
//!
//! #[derive(Clone, Debug, PartialEq, Eq)]
//! enum CalcOp {
//!     Add(i32),
//!     Multiply(i32),
//!     Get,
//! }
//!
//! impl CalcOp {
//!     fn add(n: i32) -> Free<Self, ()> {
//!         Free::suspend(Self::Add(n))
//!     }
//!
//!     fn multiply(n: i32) -> Free<Self, ()> {
//!         Free::suspend(Self::Multiply(n))
//!     }
//!
//!     fn get() -> Free<Self, i32> {
//!         Free::suspend(Self::Get)
//!     }
//! }
//!
//! // Build a computation sequence without executing side effects
//! let program = CalcOp::add(5)
//!     .then(CalcOp::multiply(3))
//!     .then(CalcOp::get());
//!
//! // Interpret the program with state.
//! // NOTE: The interpreter must return an AnyValue matching the exact return type expected
//! // by each suspended command (e.g., () for Add/Multiply, i32 for Get).
//! let mut current = 0;
//! let result: i32 = program.run(|op| match op {
//!     CalcOp::Add(n) => {
//!         current += n;
//!         Arc::new(()) as AnyValue
//!     }
//!     CalcOp::Multiply(n) => {
//!         current *= n;
//!         Arc::new(()) as AnyValue
//!     }
//!     CalcOp::Get => Arc::new(current) as AnyValue,
//! });
//!
//! assert_eq!(result, 15);
//!
//! // Because Free is Clone, the same program can be run again!
//! let mut current2 = 10;
//! let result2: i32 = program.run(|op| match op {
//!     CalcOp::Add(n) => {
//!         current2 += n;
//!         Arc::new(()) as AnyValue
//!     }
//!     CalcOp::Multiply(n) => {
//!         current2 *= n;
//!         Arc::new(()) as AnyValue
//!     }
//!     CalcOp::Get => Arc::new(current2) as AnyValue,
//! });
//! assert_eq!(result2, 45); // (10 + 5) * 3 = 45
//! ```

use std::any::Any;
use std::fmt;
use std::sync::Arc;

use crate::datatypes::error::FreeError;
use crate::datatypes::io::IO;

/// Type alias for thread-safe type-erased values in the Free monad.
pub type AnyValue = Arc<dyn Any + Send + Sync>;

/// Type alias for a continuation function in the Free monad trampoline.
pub type ContFn<F> = Arc<dyn Fn(AnyValue) -> Free<F, AnyValue> + Send + Sync + 'static>;

/// Type alias for the continuation stack used in iterative trampoline evaluation.
pub type ContStack<F> = Vec<ContFn<F>>;

/// The `Free` monad represents a computation tree separating AST construction from interpretation.
#[derive(Clone)]
pub enum Free<F, A> {
    /// A pure computation returning an immediate value.
    Pure(A),
    /// A suspended effect command with a leaf continuation mapping the interpreter's output to `A`.
    Suspend(
        F,
        Arc<dyn Fn(AnyValue) -> Result<A, &'static str> + Send + Sync + 'static>,
    ),
    /// A sequenced computation: the left sub-computation followed by a continuation.
    Bind(
        Arc<Free<F, AnyValue>>,
        Arc<dyn Fn(AnyValue) -> Free<F, A> + Send + Sync + 'static>,
    ),
}

impl<F, A> Free<F, A> {
    /// Creates a pure computation containing the given value.
    #[inline]
    pub fn pure(val: A) -> Self {
        Free::Pure(val)
    }

    /// Suspends an effect command into a `Free` computation.
    ///
    /// The interpreter is expected to return an [`AnyValue`] containing a value of type `A`.
    ///
    /// # Panics
    ///
    /// Panics during evaluation via [`run`](Self::run) if the interpreter returns a value whose
    /// type does not match `A`. For safe error handling without panics, use [`try_run`](Self::try_run).
    #[inline]
    pub fn suspend(effect: F) -> Self
    where
        A: Send + Sync + Clone + 'static,
    {
        Free::Suspend(
            effect,
            Arc::new(|any_val: AnyValue| {
                any_val
                    .downcast_ref::<A>()
                    .cloned()
                    .ok_or_else(std::any::type_name::<A>)
            }),
        )
    }

    /// Suspends an effect command with a custom continuation function.
    #[inline]
    pub fn suspend_with<Cont>(effect: F, cont: Cont) -> Self
    where
        Cont: Fn(AnyValue) -> A + Send + Sync + 'static,
    {
        Free::Suspend(effect, Arc::new(move |any_val| Ok(cont(any_val))))
    }

    /// Converts this `Free` value into a type-erased `Free<F, AnyValue>`.
    #[inline]
    pub fn into_any(&self) -> Free<F, AnyValue>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
    {
        match self {
            Free::Pure(a) => Free::Pure(Arc::new(a.clone()) as AnyValue),
            Free::Suspend(cmd, cont) => {
                let cont_clone = Arc::clone(cont);
                Free::Suspend(
                    cmd.clone(),
                    Arc::new(move |res| {
                        let a = cont_clone(res)?;
                        let a_any = &a as &dyn Any;
                        if let Some(already_arc) = a_any.downcast_ref::<AnyValue>() {
                            Ok(already_arc.clone())
                        } else {
                            Ok(Arc::new(a) as AnyValue)
                        }
                    }),
                )
            },
            Free::Bind(sub, cont) => {
                let cont_clone = Arc::clone(cont);
                Free::Bind(
                    Arc::clone(sub),
                    Arc::new(move |res| cont_clone(res).into_any()),
                )
            },
        }
    }

    /// Maps a function over the pure value of the `Free` monad.
    pub fn fmap<B, Func>(&self, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A) -> B + Send + Sync + 'static,
    {
        match self {
            Free::Pure(a) => Free::Pure(f(a.clone())),
            Free::Suspend(cmd, cont) => {
                let f_arc = Arc::new(f);
                let cont_clone = Arc::clone(cont);
                Free::Suspend(
                    cmd.clone(),
                    Arc::new(move |res| cont_clone(res).map(|a| f_arc(a))),
                )
            },
            other => {
                let f_arc = Arc::new(f);
                other.bind(move |a| Free::Pure(f_arc(a)))
            },
        }
    }

    /// Alias for [`fmap`](Self::fmap).
    #[inline]
    pub fn map<B, Func>(&self, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A) -> B + Send + Sync + 'static,
    {
        self.fmap(f)
    }

    /// Sequences another `Free` computation from the result of this computation.
    ///
    /// If `self` is `Free::Pure(a)`, `f(a)` is evaluated immediately without allocating
    /// an intermediate `Bind` node. Otherwise, a structural `Bind` node is created,
    /// enabling stack-safe trampoline evaluation in [`run`](Self::run).
    pub fn bind<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        match self {
            Free::Pure(a) => f(a.clone()),
            other => {
                let f_arc = Arc::new(f);
                Free::Bind(
                    Arc::new(other.into_any()),
                    Arc::new(move |any_val: AnyValue| {
                        let a = any_val
                            .downcast_ref::<A>()
                            .expect("Free bind downcast failed");
                        f_arc(a.clone())
                    }),
                )
            },
        }
    }

    /// Alias for [`bind`](Self::bind).
    #[inline]
    pub fn flat_map<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        self.bind(f)
    }

    /// Alias for [`bind`](Self::bind).
    #[inline]
    pub fn and_then<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        self.bind(f)
    }

    /// Sequences another `Free` computation, discarding the result of the current computation.
    #[inline]
    pub fn then<B>(&self, next: Free<F, B>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
    {
        let next_clone = next;
        self.bind(move |_| next_clone.clone())
    }

    /// Applies a function inside a `Free` computation to a value in another `Free` computation.
    pub fn apply<T, B>(&self, value: Free<F, T>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Fn(T) -> B + Send + Sync + Clone + 'static,
        T: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
    {
        let value_clone = value;
        self.bind(move |f| {
            let f_arc = Arc::new(f);
            value_clone.fmap(move |t| f_arc(t))
        })
    }

    /// Combines this computation with another using a binary function.
    pub fn zip_with<T2, B, Func>(&self, other: Free<F, T2>, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        T2: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A, T2) -> B + Send + Sync + 'static,
    {
        let f_arc = Arc::new(f);
        let other_clone = other;
        self.bind(move |a| {
            let f_clone = Arc::clone(&f_arc);
            let a_clone = a.clone();
            other_clone.fmap(move |b| f_clone(a_clone.clone(), b))
        })
    }

    /// Combines two `Free` computations using a binary function.
    pub fn lift2<T1, T2, B, Func>(f: Func, fa: Free<F, T1>, fb: Free<F, T2>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        T1: Send + Sync + Clone + 'static,
        T2: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(T1, T2) -> B + Send + Sync + 'static,
    {
        fa.zip_with(fb, f)
    }

    /// Unified internal trampoline engine powering both [`run`](Self::run) and [`try_run`](Self::try_run).
    fn run_internal<Interp, E>(&self, mut interp: Interp) -> Result<A, FreeError<E>>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> Result<AnyValue, E>,
    {
        let mut cur: Free<F, AnyValue> = self.into_any();
        let mut stack: ContStack<F> = Vec::new();

        loop {
            match cur {
                Free::Bind(ref sub, ref cont) => {
                    stack.push(Arc::clone(cont));
                    cur = (**sub).clone();
                },
                Free::Pure(ref val) => match stack.pop() {
                    Some(cont) => {
                        cur = cont(Arc::clone(val));
                    },
                    None => {
                        return val
                            .downcast_ref::<A>()
                            .cloned()
                            .ok_or(FreeError::TypeMismatch {
                                expected: std::any::type_name::<A>(),
                            });
                    },
                },
                Free::Suspend(ref cmd, ref cont) => {
                    let effect_res = interp(cmd.clone()).map_err(FreeError::Interpreter)?;
                    let any_box = cont(effect_res)
                        .map_err(|expected| FreeError::TypeMismatch { expected })?;
                    match stack.pop() {
                        Some(cont) => {
                            cur = cont(any_box);
                        },
                        None => {
                            return any_box.downcast_ref::<A>().cloned().ok_or(
                                FreeError::TypeMismatch {
                                    expected: std::any::type_name::<A>(),
                                },
                            );
                        },
                    }
                },
            }
        }
    }

    /// Evaluates the `Free` computation to completion using an effect interpreter.
    ///
    /// Evaluation is performed using an iterative trampoline stack, ensuring $O(N)$ linear
    /// execution time and $O(1)$ call stack depth without risking call stack overflow.
    ///
    /// # Panics
    ///
    /// The interpreter must return an [`AnyValue`] matching the exact return type expected by
    /// each effect. If a type mismatch occurs, execution panics with a descriptive error message.
    /// To handle type mismatches gracefully as `Result`, use [`try_run`](Self::try_run).
    pub fn run<Interp>(&self, mut interp: Interp) -> A
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> AnyValue,
    {
        match self.run_internal(|cmd| Ok::<_, std::convert::Infallible>(interp(cmd))) {
            Ok(val) => val,
            Err(FreeError::TypeMismatch { expected }) => {
                panic!("Free interpretation type mismatch: expected return type {expected}")
            },
            Err(FreeError::Interpreter(inf)) => match inf {},
        }
    }

    /// Evaluates the `Free` computation with a fallible effect interpreter.
    ///
    /// Returns `Err(FreeError::Interpreter(e))` if the interpreter returns an error, or
    /// `Err(FreeError::TypeMismatch)` if the effect payload does not match the expected type.
    pub fn try_run<Interp, E>(&self, interp: Interp) -> Result<A, FreeError<E>>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> Result<AnyValue, E>,
    {
        self.run_internal(interp)
    }

    /// Interprets this `Free` computation into an [`IO`] computation via a natural transformation.
    ///
    /// Returns a lazy [`IO`] computation whose effects run only when executed via [`IO::run`].
    pub fn fold_map<Morphism>(&self, interp: Morphism) -> IO<A>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Morphism: Fn(F) -> IO<AnyValue> + Send + Sync + Clone + 'static,
    {
        let this = self.clone();
        IO::new(move || {
            let interp_clone = interp.clone();
            this.run(move |cmd| interp_clone(cmd).run())
        })
    }

    /// Returns `true` if this computation is a pure value.
    #[inline]
    pub const fn is_pure(&self) -> bool {
        matches!(self, Free::Pure(_))
    }

    /// Returns `true` if this computation is a suspended leaf effect command.
    #[inline]
    pub const fn is_suspend(&self) -> bool {
        matches!(self, Free::Suspend(_, _))
    }

    /// Returns `true` if this computation is a sequenced continuation node.
    #[inline]
    pub const fn is_bind(&self) -> bool {
        matches!(self, Free::Bind(_, _))
    }

    /// Returns a reference to the inner value if it is pure.
    #[inline]
    pub fn as_pure(&self) -> Option<&A> {
        match self {
            Free::Pure(a) => Some(a),
            Free::Suspend(_, _) | Free::Bind(_, _) => None,
        }
    }

    /// Extracts the inner value if it is pure.
    #[inline]
    pub fn into_pure(&self) -> Option<A>
    where
        A: Clone,
    {
        match self {
            Free::Pure(a) => Some(a.clone()),
            Free::Suspend(_, _) | Free::Bind(_, _) => None,
        }
    }
}

impl<F: fmt::Debug, A: fmt::Debug> fmt::Debug for Free<F, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Free::Pure(a) => f.debug_tuple("Pure").field(a).finish(),
            Free::Suspend(cmd, _) => f
                .debug_tuple("Suspend")
                .field(cmd)
                .field(&"<continuation>")
                .finish(),
            Free::Bind(sub, _) => {
                let mut depth = 1usize;
                let mut cur: &Free<F, AnyValue> = sub;
                while let Free::Bind(next, _) = cur {
                    depth += 1;
                    cur = next;
                    if depth > 10 {
                        break;
                    }
                }
                if depth > 10 {
                    while let Free::Bind(next, _) = cur {
                        depth += 1;
                        cur = next;
                    }
                    f.debug_tuple("Bind")
                        .field(&format_args!("depth: {depth}"))
                        .field(&"<continuation>")
                        .finish()
                } else {
                    f.debug_tuple("Bind")
                        .field(sub)
                        .field(&"<continuation>")
                        .finish()
                }
            },
        }
    }
}

impl<F, A: Default> Default for Free<F, A> {
    #[inline]
    fn default() -> Self {
        Free::Pure(A::default())
    }
}

impl<F, A> Drop for Free<F, A> {
    fn drop(&mut self) {
        if let Free::Bind(sub, _) = self {
            let mut cur = Arc::clone(sub);
            *sub = Arc::new(Free::Pure(Arc::new(()) as AnyValue));
            while let Ok(mut node) = Arc::try_unwrap(cur) {
                if let Free::Bind(ref mut next, _) = node {
                    let next_arc = Arc::clone(next);
                    *next = Arc::new(Free::Pure(Arc::new(()) as AnyValue));
                    cur = next_arc;
                } else {
                    break;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum TestCmd {
        Increment(i32),
        Fetch,
    }

    #[test]
    fn test_pure_value() {
        let computation: Free<TestCmd, i32> = Free::pure(42);
        assert!(computation.is_pure());
        assert!(!computation.is_suspend());
        assert!(!computation.is_bind());
        assert_eq!(computation.as_pure(), Some(&42));
        assert_eq!(computation.into_pure(), Some(42));
    }

    #[test]
    fn test_fmap() {
        let computation: Free<TestCmd, i32> = Free::pure(21).fmap(|x| x * 2);
        assert_eq!(computation.into_pure(), Some(42));
    }

    #[test]
    fn test_bind_sequence() {
        let computation: Free<TestCmd, i32> = Free::pure(10)
            .bind(|x| Free::pure(x + 5))
            .flat_map(|x| Free::pure(x * 2));
        assert_eq!(computation.into_pure(), Some(30));
    }

    #[test]
    fn test_suspend_and_run() {
        let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .bind(|_: ()| Free::<TestCmd, ()>::suspend(TestCmd::Increment(25)))
            .bind(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .bind(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .bind(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
        let err_res: Result<i32, FreeError<&'static str>> =
            failing_program.try_run(|cmd| match cmd {
                TestCmd::Increment(_) => Err("error during increment"),
                TestCmd::Fetch => Ok(Arc::new(0) as AnyValue),
            });
        assert_eq!(
            err_res,
            Err(FreeError::Interpreter("error during increment"))
        );

        // Counterexample for P3: Type mismatch returns Err(FreeError::TypeMismatch) instead of panicking
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
        use std::sync::atomic::{AtomicU32, Ordering};
        let side_effect_count = Arc::new(AtomicU32::new(0));
        let count_clone = Arc::clone(&side_effect_count);

        // AST construction carries static types Free<TestCmd, ()> and Free<TestCmd, i32>
        let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        // Interpreter author accidentally returns String instead of expected i32
        // Notice this compiles without any compiler error!
        let res: Result<i32, FreeError<()>> = program.try_run(move |cmd| match cmd {
            TestCmd::Increment(_) => {
                count_clone.fetch_add(1, Ordering::SeqCst);
                Ok(Arc::new(()) as AnyValue)
            }
            TestCmd::Fetch => Ok(Arc::new(String::from("wrong_type")) as AnyValue),
        });

        // Verifies: 1) First step already ran and executed its side effect at runtime
        assert_eq!(side_effect_count.load(Ordering::SeqCst), 1);
        // Verifies: 2) Error is only detected at runtime when Fetch continuation downcasts AnyValue
        assert!(matches!(
            res,
            Err(FreeError::TypeMismatch { expected }) if expected == std::any::type_name::<i32>()
        ));
    }

    #[test]
    #[should_panic(expected = "Free interpretation type mismatch: expected return type i32")]
    fn test_run_panics_on_runtime_type_mismatch() {
        let program = Free::<TestCmd, i32>::suspend(TestCmd::Fetch);
        // Compiles successfully, but panics at runtime during downcasting
        let _: i32 = program.run(|_| Arc::new("wrong_type") as AnyValue);
    }

    #[test]
    fn test_apply_and_lift2() {
        let func: Free<TestCmd, fn(i32) -> i32> = Free::pure(|x: i32| x + 10);
        let val: Free<TestCmd, i32> = Free::pure(5);
        let applied = func.apply(val);
        assert_eq!(applied.into_pure(), Some(15));

        let fa: Free<TestCmd, i32> = Free::pure(3);
        let fb: Free<TestCmd, i32> = Free::pure(4);
        let combined: Free<TestCmd, i32> = Free::<TestCmd, ()>::lift2(|a, b| a * b, fa, fb);
        assert_eq!(combined.into_pure(), Some(12));

        let fa2: Free<TestCmd, i32> = Free::pure(3);
        let fb2: Free<TestCmd, i32> = Free::pure(4);
        let zipped = fa2.zip_with(fb2, |a, b| a + b);
        assert_eq!(zipped.into_pure(), Some(7));
    }

    #[test]
    fn test_monad_laws() {
        // Left identity: pure(a).bind(f) == f(a)
        let a = 7;
        let f = |x: i32| Free::pure(x * 3);
        let left: Free<TestCmd, i32> = Free::pure(a).bind(f);
        let right = f(a);
        assert_eq!(left.into_pure(), right.into_pure());

        // Right identity: m.bind(pure) == m
        let m: Free<TestCmd, i32> = Free::pure(42);
        let bound = m.bind(Free::pure);
        assert_eq!(bound.into_pure(), Some(42));

        // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
        let g = |x: i32| Free::pure(x + 100);
        let m1: Free<TestCmd, i32> = Free::pure(5);
        let m2: Free<TestCmd, i32> = Free::pure(5);
        let r1 = m1.bind(f).bind(g);
        let r2 = m2.bind(move |x| f(x).bind(g));
        assert_eq!(r1.into_pure(), r2.into_pure());
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

        // Run 1: with normal counter
        let mut c1 = 0;
        let r1: i32 = program.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c1 += n;
                Arc::new(()) as AnyValue
            },
            TestCmd::Fetch => Arc::new(c1) as AnyValue,
        });
        assert_eq!(r1, 30);

        // Run 2: same program instance executed with a different initial counter
        let mut c2 = 100;
        let r2: i32 = program.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c2 += n;
                Arc::new(()) as AnyValue
            },
            TestCmd::Fetch => Arc::new(c2) as AnyValue,
        });
        assert_eq!(r2, 130);

        // Branching: clone program and extend it in two different directions
        let branch_a = program.clone().bind(|total: i32| Free::pure(total * 2));
        let branch_b = program.bind(|total: i32| Free::pure(total + 1000));

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
    fn test_fold_map_to_io() {
        let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
            .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        let io_comp = program.fold_map(|cmd| {
            IO::new(move || match cmd {
                TestCmd::Increment(_) => Arc::new(()) as AnyValue,
                TestCmd::Fetch => Arc::new(42_i32) as AnyValue,
            })
        });

        // Cold IO execution
        assert_eq!(io_comp.run(), 42);
    }

    #[test]
    fn test_debug_format() {
        let pure_val: Free<TestCmd, i32> = Free::pure(99);
        assert_eq!(format!("{pure_val:?}"), "Pure(99)");

        let bound: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        assert_eq!(
            format!("{bound:?}"),
            "Suspend(Increment(1), \"<continuation>\")"
        );
    }

    #[test]
    fn test_deep_debug_format_stack_safety() {
        // Counterexample for P2: 50,000-deep spine Debug formatting must not overflow the stack
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let debug_str = format!("{p:?}");
        assert!(debug_str.contains("depth: 50000"));
    }
}
