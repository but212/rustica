//! # Free Monad
//!
//! `Free<F, A>` represents a computation tree of commands `F`, separating program
//! definition from execution.
//!
//! ## Execution and Stack Safety
//!
//! - **Evaluation**: Evaluated with [`run`](Free::run) or [`try_run`](Free::try_run). An internal
//!   stack unwinds left-associated chains (`a.then(b).then(c)`), keeping call stack frames $O(1)$.
//! - **Error handling**: [`try_run`](Free::try_run) returns [`FreeError`] on interpreter error or
//!   interpreter-originated downcast mismatch instead of panicking.
//! - **Drop and Debug**: Traverses nested chains iteratively to avoid stack overflow when
//!   dropping or formatting deep programs.
//! - **Reuse**: Backed by `Arc`, so programs can be cloned and run multiple times.
//!
//! ## Architectural Role: `Free` vs `Program`
//!
//! Rustica provides two distinct mechanisms for command-oriented programming:
//!
//! - **`Free<F, A>` (DSL AST Engine)**: Construct cloneable computation trees.
//!   Backed by `Arc`, a `Free` AST can be cloned and interpreted by different backends
//!   (e.g., dry-run simulator vs real execution). Node shape is inspectable via
//!   [`is_pure`](Free::is_pure), [`is_suspend`](Free::is_suspend), [`is_bind`](Free::is_bind),
//!   and [`is_then`](Free::is_then); effect commands can be inspected via [`as_suspend`](Free::as_suspend),
//!   pure values via [`as_pure`](Free::as_pure), and static sequencing trees via [`as_then`](Free::as_then).
//!   Dynamic continuations (`Bind`) remain opaque. Stack safety applies to `Bind` and `Then` AST spines.
//!   It is fully supported and intentionally designed for reusable DSLs.
//! - **[`Program<H, A>`](crate::datatypes::operational::Program) (Operational Pipeline)**:
//!   Statically couples commands to a specific handler `H` at compile time, eliminating runtime
//!   downcasts in the user handler interface with trampoline evaluation.
//!
//! ## Example
//!
//! ```rust
//! use rustica::datatypes::free::{any_value, AnyValue, Free};
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
//! let program = CalcOp::add(5)
//!     .then(CalcOp::multiply(3))
//!     .then(CalcOp::get());
//!
//! let mut current = 0;
//! let result: i32 = program.run(|op| match op {
//!     CalcOp::Add(n) => {
//!         current += n;
//!         any_value(())
//!     }
//!     CalcOp::Multiply(n) => {
//!         current *= n;
//!         any_value(())
//!     }
//!     CalcOp::Get => any_value(current),
//! });
//!
//! assert_eq!(result, 15);
//!
//! // The same program can be evaluated again with different state
//! let mut current2 = 10;
//! let result2: i32 = program.run(|op| match op {
//!     CalcOp::Add(n) => {
//!         current2 += n;
//!         any_value(())
//!     }
//!     CalcOp::Multiply(n) => {
//!         current2 *= n;
//!         any_value(())
//!     }
//!     CalcOp::Get => any_value(current2),
//! });
//! assert_eq!(result2, 45); // (10 + 5) * 3 = 45
//! ```

use std::any::Any;
use std::fmt::{self, Display};
use std::sync::Arc;

/// Errors that can occur during [`Free`] evaluation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FreeError<E> {
    /// An error returned by the effect interpreter.
    Interpreter(E),
    /// A type mismatch when downcasting the effect result.
    TypeMismatch {
        /// The type expected by the Free continuation.
        expected: &'static str,
    },
}

impl<E> FreeError<E> {
    /// Returns `true` if this error is from the interpreter.
    #[inline]
    pub const fn is_interpreter(&self) -> bool {
        matches!(self, FreeError::Interpreter(_))
    }

    /// Returns `true` if this error is a type mismatch.
    #[inline]
    pub const fn is_type_mismatch(&self) -> bool {
        matches!(self, FreeError::TypeMismatch { .. })
    }
}

impl<E: Display> Display for FreeError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreeError::Interpreter(e) => write!(f, "Free interpreter error: {e}"),
            FreeError::TypeMismatch { expected } => {
                write!(
                    f,
                    "Free interpretation type mismatch: expected return type {expected}"
                )
            },
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for FreeError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FreeError::Interpreter(e) => Some(e),
            FreeError::TypeMismatch { .. } => None,
        }
    }
}

/// Type alias for thread-safe type-erased values in the Free monad.
pub type AnyValue = Arc<dyn Any + Send + Sync>;

/// Wraps a value into an [`AnyValue`] for effect interpreter return values.
///
/// Reduces boilerplate when returning values from effect interpreters in [`Free::run`]
/// and [`Free::try_run`], avoiding repeated `Arc::new(x) as AnyValue`.
///
/// # Example
///
/// ```rust
/// use rustica::datatypes::free::{any_value, AnyValue};
///
/// let val: AnyValue = any_value(42_i32);
/// assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
/// ```
#[inline]
pub fn any_value<T: Any + Send + Sync>(v: T) -> AnyValue {
    Arc::new(v)
}

/// Type alias for a continuation function in the Free monad trampoline.
pub type ContFn<F> = Arc<dyn Fn(AnyValue) -> Free<F, AnyValue> + Send + Sync + 'static>;

/// Evaluation frame used in iterative trampoline execution.
enum Frame<F> {
    BindCont(ContFn<F>),
    ThenNext(Arc<Free<F, AnyValue>>),
}

/// Internal AST node representation for [`Free`].
#[derive(Clone)]
enum Node<F, A> {
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
    /// A value-independent sequenced computation: left sub-computation followed by right sub-computation.
    Then(Arc<Free<F, AnyValue>>, Arc<Free<F, AnyValue>>),
}

/// The `Free` monad represents a computation tree separating AST construction from interpretation.
#[derive(Clone)]
#[repr(transparent)]
pub struct Free<F, A> {
    node: Option<Node<F, A>>,
}

#[inline]
fn unwrap_arc<T: Clone>(arc: Arc<T>) -> T {
    Arc::try_unwrap(arc).unwrap_or_else(|a| (*a).clone())
}

impl<F, A> Free<F, A> {
    #[inline]
    const fn from_node(node: Node<F, A>) -> Self {
        Self { node: Some(node) }
    }

    #[inline]
    fn node(&self) -> &Node<F, A> {
        self.node.as_ref().expect("Free node already consumed")
    }

    #[inline]
    fn take_node(&mut self) -> Node<F, A> {
        self.node.take().expect("Free node already consumed")
    }

    fn push_node_children(node: Node<F, A>, stack: &mut Vec<Arc<Free<F, AnyValue>>>) {
        match node {
            Node::Pure(_) | Node::Suspend(_, _) => {},
            Node::Bind(sub, _) => {
                stack.push(sub);
            },
            Node::Then(left, right) => {
                stack.push(right);
                stack.push(left);
            },
        }
    }

    /// Creates a pure computation containing the given value.
    #[inline]
    pub const fn pure(val: A) -> Self {
        Self::from_node(Node::Pure(val))
    }

    /// Suspends an effect command into a `Free` computation.
    ///
    /// The interpreter is expected to return an [`AnyValue`] containing a value of type `A`.
    ///
    /// # Panics
    ///
    /// Panics during evaluation via [`run`](Self::run) if the interpreter returns a value whose
    /// type does not match `A`. For safe error handling without panics on interpreter-originated
    /// mismatches, use [`try_run`](Self::try_run).
    #[inline]
    pub fn suspend(effect: F) -> Self
    where
        A: Send + Sync + Clone + 'static,
    {
        Self::from_node(Node::Suspend(
            effect,
            Arc::new(|any_val: AnyValue| {
                let any_ref = &any_val as &dyn Any;
                if let Some(val) = any_ref.downcast_ref::<A>() {
                    return Ok(val.clone());
                }
                any_val
                    .downcast_ref::<A>()
                    .cloned()
                    .ok_or_else(std::any::type_name::<A>)
            }),
        ))
    }

    /// Suspends an effect command with a custom continuation function.
    #[inline]
    pub fn suspend_with<Cont>(effect: F, cont: Cont) -> Self
    where
        Cont: Fn(AnyValue) -> A + Send + Sync + 'static,
    {
        Self::from_node(Node::Suspend(
            effect,
            Arc::new(move |any_val| Ok(cont(any_val))),
        ))
    }

    /// Converts this `Free` value into a type-erased `Free<F, AnyValue>`.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn into_any(&self) -> Free<F, AnyValue>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
    {
        // Double-erasure defense: if self is already Free<F, AnyValue>, do an O(1) Arc clone directly.
        if let Some(erased) = (self as &dyn Any).downcast_ref::<Free<F, AnyValue>>() {
            return erased.clone();
        }

        match self.node() {
            Node::Pure(a) => Free::from_node(Node::Pure(Arc::new(a.clone()) as AnyValue)),
            Node::Suspend(cmd, cont) => {
                let cont_clone = Arc::clone(cont);
                Free::from_node(Node::Suspend(
                    cmd.clone(),
                    Arc::new(move |res| {
                        let a = cont_clone(res)?;
                        Ok(Arc::new(a) as AnyValue)
                    }),
                ))
            },
            Node::Bind(sub, cont) => {
                let cont_clone = Arc::clone(cont);
                Free::from_node(Node::Bind(
                    Arc::clone(sub),
                    Arc::new(move |res| cont_clone(res).into_any()),
                ))
            },
            Node::Then(left, right) => {
                Free::from_node(Node::Then(Arc::clone(left), Arc::clone(right)))
            },
        }
    }

    /// Maps a function over the pure value of the `Free` monad.
    pub fn map<B, Func>(&self, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A) -> B + Send + Sync + 'static,
    {
        match self.node() {
            Node::Pure(a) => Free::pure(f(a.clone())),
            Node::Suspend(cmd, cont) => {
                let f_arc = Arc::new(f);
                let cont_clone = Arc::clone(cont);
                Free::from_node(Node::Suspend(
                    cmd.clone(),
                    Arc::new(move |res| cont_clone(res).map(|a| f_arc(a))),
                ))
            },
            _ => {
                let f_arc = Arc::new(f);
                self.and_then(move |a| Free::pure(f_arc(a)))
            },
        }
    }

    /// Functional alias for [`map`](Self::map).
    #[deprecated(
        since = "0.19.0",
        note = "use `map` instead; scheduled for removal in 0.20.0"
    )]
    #[inline]
    pub fn fmap<B, Func>(&self, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A) -> B + Send + Sync + 'static,
    {
        self.map(f)
    }

    /// Sequences another `Free` computation from the result of this computation.
    ///
    /// If `self` is pure, `f(a)` is evaluated immediately without allocating
    /// an intermediate `Bind` node. Otherwise, a structural `Bind` node is created,
    /// enabling stack-safe trampoline evaluation in [`run`](Self::run).
    pub fn and_then<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        match self.node() {
            Node::Pure(a) => f(a.clone()),
            _ => {
                let f_arc = Arc::new(f);
                let sub = Arc::new(self.into_any());
                Free::from_node(Node::Bind(
                    sub,
                    Arc::new(move |any_val: AnyValue| {
                        let any_ref = &any_val as &dyn Any;
                        if let Some(val) = any_ref.downcast_ref::<A>() {
                            return f_arc(val.clone());
                        }
                        let a = any_val
                            .downcast_ref::<A>()
                            .expect("Free bind downcast failed");
                        f_arc(a.clone())
                    }),
                ))
            },
        }
    }

    /// Alias for [`and_then`](Self::and_then).
    #[deprecated(
        since = "0.19.0",
        note = "use `and_then` instead; scheduled for removal in 0.20.0"
    )]
    #[inline]
    pub fn bind<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        self.and_then(f)
    }

    /// Alias for [`and_then`](Self::and_then).
    #[deprecated(
        since = "0.19.0",
        note = "use `and_then` instead; scheduled for removal in 0.20.0"
    )]
    #[inline]
    pub fn flat_map<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        self.and_then(f)
    }

    /// Sequences another `Free` computation, discarding the result of the current computation.
    ///
    /// Constructs a structural `Then` AST node representing value-independent sequencing.
    /// If `self` is a pure computation, `next` is returned immediately without allocating a `Then` node.
    #[inline]
    pub fn then<B>(&self, next: Free<F, B>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
    {
        if self.is_pure() {
            return next;
        }
        let left = Arc::new(self.into_any());
        let right = Arc::new(next.into_any());
        Free::from_node(Node::Then(left, right))
    }

    /// Applies a function inside a `Free` computation to a value in another `Free` computation.
    pub fn apply<T, B>(&self, value: Free<F, T>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Fn(T) -> B + Send + Sync + Clone + 'static,
        T: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
    {
        self.and_then(move |f| {
            let f_arc = Arc::new(f);
            value.map(move |t| f_arc(t))
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
        self.and_then(move |a| {
            let f_clone = Arc::clone(&f_arc);
            other.map(move |b| f_clone(a.clone(), b))
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
        let mut cur: Node<F, AnyValue> = self.into_any().take_node();
        let mut stack: Vec<Frame<F>> = Vec::new();

        loop {
            match cur {
                Node::Bind(sub, cont) => {
                    stack.push(Frame::BindCont(cont));
                    cur = unwrap_arc(sub).take_node();
                },
                Node::Then(left, right) => {
                    stack.push(Frame::ThenNext(right));
                    cur = unwrap_arc(left).take_node();
                },
                Node::Pure(val) => match stack.pop() {
                    Some(Frame::BindCont(cont)) => {
                        cur = cont(val).take_node();
                    },
                    Some(Frame::ThenNext(next_comp)) => {
                        cur = unwrap_arc(next_comp).take_node();
                    },
                    None => {
                        let any_ref = &val as &dyn Any;
                        if let Some(a_ref) = any_ref.downcast_ref::<A>() {
                            return Ok(a_ref.clone());
                        }
                        return val
                            .downcast_ref::<A>()
                            .cloned()
                            .ok_or(FreeError::TypeMismatch {
                                expected: std::any::type_name::<A>(),
                            });
                    },
                },
                Node::Suspend(cmd, cont) => {
                    let effect_res = interp(cmd.clone()).map_err(FreeError::Interpreter)?;
                    let any_box = cont(effect_res)
                        .map_err(|expected| FreeError::TypeMismatch { expected })?;
                    match stack.pop() {
                        Some(Frame::BindCont(next_cont)) => {
                            cur = next_cont(any_box).take_node();
                        },
                        Some(Frame::ThenNext(next_comp)) => {
                            cur = unwrap_arc(next_comp).take_node();
                        },
                        None => {
                            let any_ref = &any_box as &dyn Any;
                            if let Some(a_ref) = any_ref.downcast_ref::<A>() {
                                return Ok(a_ref.clone());
                            }
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

    /// Evaluates the computation using an effect interpreter.
    ///
    /// Evaluation unwinds chains iteratively, keeping call stack depth $O(1)$.
    ///
    /// # Panics
    ///
    /// Panics if the interpreter returns an [`AnyValue`] that does not match the expected type `A`.
    /// Use [`try_run`](Self::try_run) to handle interpreter-originated mismatches as a `Result`.
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
    /// `Err(FreeError::TypeMismatch)` if the effect payload returned by the interpreter does
    /// not match the expected type (returning `Err` instead of panicking on interpreter-originated mismatches).
    pub fn try_run<Interp, E>(&self, interp: Interp) -> Result<A, FreeError<E>>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> Result<AnyValue, E>,
    {
        self.run_internal(interp)
    }

    /// Returns `true` if this computation is a pure value.
    #[inline]
    pub const fn is_pure(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Pure(_)))
    }

    /// Returns `true` if this computation is a suspended leaf effect command.
    #[inline]
    pub const fn is_suspend(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Suspend(_, _)))
    }

    /// Returns `true` if this computation is a sequenced continuation node.
    #[inline]
    pub const fn is_bind(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Bind(_, _)))
    }

    /// Returns `true` if this computation is a value-independent sequencing node.
    #[inline]
    pub const fn is_then(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Then(_, _)))
    }

    /// Returns a reference to the inner value if it is pure.
    #[inline]
    pub const fn as_pure(&self) -> Option<&A> {
        match self.node.as_ref() {
            Some(Node::Pure(a)) => Some(a),
            _ => None,
        }
    }

    /// Clones and extracts the inner value if it is pure.
    ///
    /// Following the Rustica API Guidelines (C-CONV), this method is named `to_pure`
    /// because it clones the inner value from an immutable reference `&self`.
    #[inline]
    pub fn to_pure(&self) -> Option<A>
    where
        A: Clone,
    {
        self.as_pure().cloned()
    }

    /// Returns a reference to the inner effect command if this computation is a suspended leaf effect.
    #[inline]
    pub const fn as_suspend(&self) -> Option<&F> {
        match self.node.as_ref() {
            Some(Node::Suspend(cmd, _)) => Some(cmd),
            _ => None,
        }
    }

    /// Returns references to the left and right sub-computations if this is a `Then` sequencing node.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn as_then(&self) -> Option<(&Free<F, AnyValue>, &Free<F, AnyValue>)> {
        match self.node.as_ref() {
            Some(Node::Then(left, right)) => Some((left.as_ref(), right.as_ref())),
            _ => None,
        }
    }
}

const MAX_DEBUG_RECURSION: usize = 8;

struct DebugFree<'a, F, A>(&'a Free<F, A>, usize);

impl<'a, F: fmt::Debug, A: fmt::Debug> fmt::Debug for DebugFree<'a, F, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_free(self.0, f, self.1)
    }
}

fn fmt_free<F: fmt::Debug, A: fmt::Debug>(
    free: &Free<F, A>, f: &mut fmt::Formatter<'_>, depth: usize,
) -> fmt::Result {
    let node = free.node();
    if depth >= MAX_DEBUG_RECURSION {
        return match node {
            Node::Pure(_) => write!(f, "Pure(..)"),
            Node::Suspend(cmd, _) => f.debug_tuple("Suspend").field(cmd).field(&"..").finish(),
            Node::Bind(_, _) => write!(f, "Bind(..)"),
            Node::Then(_, _) => write!(f, "Then(..)"),
        };
    }

    match node {
        Node::Pure(a) => f.debug_tuple("Pure").field(a).finish(),
        Node::Suspend(cmd, _) => f
            .debug_tuple("Suspend")
            .field(cmd)
            .field(&"<continuation>")
            .finish(),
        Node::Bind(sub, _) => {
            let mut spine_depth = 1usize;
            let mut cur: &Free<F, AnyValue> = sub;
            while let Some(Node::Bind(next, _)) = cur.node.as_ref() {
                spine_depth += 1;
                cur = next;
                if spine_depth > 10 {
                    break;
                }
            }
            if spine_depth > 10 {
                while let Some(Node::Bind(next, _)) = cur.node.as_ref() {
                    spine_depth += 1;
                    cur = next;
                }
                f.debug_tuple("Bind")
                    .field(&format_args!("depth: {spine_depth}"))
                    .field(&"<continuation>")
                    .finish()
            } else {
                f.debug_tuple("Bind")
                    .field(&DebugFree(sub, depth + 1))
                    .field(&"<continuation>")
                    .finish()
            }
        },
        Node::Then(left, right) => {
            let mut left_depth = 1usize;
            let mut cur = left;
            while let Some(Node::Then(next, _)) = cur.node.as_ref() {
                left_depth += 1;
                cur = next;
                if left_depth > 10 {
                    break;
                }
            }
            if left_depth > 10 {
                while let Some(Node::Then(next, _)) = cur.node.as_ref() {
                    left_depth += 1;
                    cur = next;
                }
            }

            let mut right_depth = 1usize;
            let mut cur = right;
            while let Some(Node::Then(_, next)) = cur.node.as_ref() {
                right_depth += 1;
                cur = next;
                if right_depth > 10 {
                    break;
                }
            }
            if right_depth > 10 {
                while let Some(Node::Then(_, next)) = cur.node.as_ref() {
                    right_depth += 1;
                    cur = next;
                }
            }

            let max_depth = left_depth.max(right_depth);
            if max_depth > 10 {
                f.debug_tuple("Then")
                    .field(&format_args!("depth: {max_depth}"))
                    .finish()
            } else {
                f.debug_tuple("Then")
                    .field(&DebugFree(left, depth + 1))
                    .field(&DebugFree(right, depth + 1))
                    .finish()
            }
        },
    }
}

impl<F: fmt::Debug, A: fmt::Debug> fmt::Debug for Free<F, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_free(self, f, 0)
    }
}

impl<F, A: Default> Default for Free<F, A> {
    #[inline]
    fn default() -> Self {
        Free::pure(A::default())
    }
}

impl<F, A> Drop for Free<F, A> {
    fn drop(&mut self) {
        if let Some(node) = self.node.take() {
            let mut stack: Vec<Arc<Free<F, AnyValue>>> = Vec::new();
            Self::push_node_children(node, &mut stack);

            while let Some(arc) = stack.pop() {
                if let Some(child_node) = Arc::into_inner(arc).and_then(|mut free| free.node.take())
                {
                    Free::<F, AnyValue>::push_node_children(child_node, &mut stack);
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
        assert_eq!(computation.to_pure(), Some(42));
    }

    #[test]
    #[allow(deprecated)]
    fn test_fmap() {
        let computation: Free<TestCmd, i32> = Free::pure(21).fmap(|x| x * 2);
        assert_eq!(computation.to_pure(), Some(42));

        let mapped: Free<TestCmd, i32> = Free::pure(21).map(|x| x * 2);
        assert_eq!(mapped.to_pure(), Some(42));
    }

    #[test]
    #[allow(deprecated)]
    fn test_bind_sequence() {
        let computation: Free<TestCmd, i32> = Free::pure(10)
            .bind(|x| Free::pure(x + 5))
            .flat_map(|x| Free::pure(x * 2));
        assert_eq!(computation.to_pure(), Some(30));

        let and_then_comp: Free<TestCmd, i32> = Free::pure(10)
            .and_then(|x| Free::pure(x + 5))
            .and_then(|x| Free::pure(x * 2));
        assert_eq!(and_then_comp.to_pure(), Some(30));
    }

    #[test]
    fn test_suspend_and_run() {
        let program = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .and_then(|_: ()| Free::<TestCmd, ()>::suspend(TestCmd::Increment(25)))
            .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

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
            .and_then(|_: ()| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
        let err_res: Result<i32, FreeError<&'static str>> =
            failing_program.try_run(|cmd| match cmd {
                TestCmd::Increment(_) => Err("error during increment"),
                TestCmd::Fetch => Ok(Arc::new(0) as AnyValue),
            });
        assert_eq!(
            err_res,
            Err(FreeError::Interpreter("error during increment"))
        );

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
            },
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
        assert_eq!(applied.to_pure(), Some(15));

        let fa: Free<TestCmd, i32> = Free::pure(3);
        let fb: Free<TestCmd, i32> = Free::pure(4);
        let combined: Free<TestCmd, i32> = Free::<TestCmd, ()>::lift2(|a, b| a * b, fa, fb);
        assert_eq!(combined.to_pure(), Some(12));

        let fa2: Free<TestCmd, i32> = Free::pure(3);
        let fb2: Free<TestCmd, i32> = Free::pure(4);
        let zipped = fa2.zip_with(fb2, |a, b| a + b);
        assert_eq!(zipped.to_pure(), Some(7));
    }

    #[test]
    #[allow(deprecated)]
    fn test_monad_laws() {
        // Left identity: pure(a).bind(f) == f(a)
        let a = 7;
        let f = |x: i32| Free::pure(x * 3);
        let left: Free<TestCmd, i32> = Free::pure(a).bind(f);
        let right = f(a);
        assert_eq!(left.to_pure(), right.to_pure());

        // and_then obeys left identity
        let left_and_then: Free<TestCmd, i32> = Free::pure(a).and_then(f);
        assert_eq!(left_and_then.to_pure(), right.to_pure());

        // Right identity: m.bind(pure) == m
        let m: Free<TestCmd, i32> = Free::pure(42);
        let bound = m.bind(Free::pure);
        assert_eq!(bound.to_pure(), Some(42));
        assert_eq!(m.and_then(Free::pure).to_pure(), Some(42));

        // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
        let g = |x: i32| Free::pure(x + 100);
        let m1: Free<TestCmd, i32> = Free::pure(5);
        let m2: Free<TestCmd, i32> = Free::pure(5);
        let r1 = m1.bind(f).bind(g);
        let r2 = m2.bind(move |x| f(x).bind(g));
        assert_eq!(r1.to_pure(), r2.to_pure());

        let r1_and_then = m1.and_then(f).and_then(g);
        let r2_and_then = m2.and_then(move |x| f(x).and_then(g));
        assert_eq!(r1_and_then.to_pure(), r2_and_then.to_pure());
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
        let branch_a = program.and_then(|total: i32| Free::pure(total * 2));
        let branch_b = program.and_then(|total: i32| Free::pure(total + 1000));

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
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let debug_str = format!("{p:?}");
        assert!(debug_str.contains("depth: 50000"));
    }

    #[test]
    fn test_deep_free_drop_with_clones() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..30_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let q = p.clone();
        // Drop clone first, then original
        drop(q);
        drop(p);

        // Now drop original first, then clone
        let mut p2: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..30_000 {
            p2 = p2.then(Free::suspend(TestCmd::Increment(1)));
        }
        let q2 = p2.clone();
        drop(p2);
        drop(q2);
    }

    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    struct CloneCountingCmd {
        id: usize,
        clones: Arc<AtomicUsize>,
    }

    impl Clone for CloneCountingCmd {
        fn clone(&self) -> Self {
            self.clones.fetch_add(1, Ordering::SeqCst);
            Self {
                id: self.id,
                clones: Arc::clone(&self.clones),
            }
        }
    }

    #[test]
    fn test_free_trampoline_unshared_bind_no_clone() {
        let counter = Arc::new(AtomicUsize::new(0));
        let cmd = CloneCountingCmd {
            id: 10,
            clones: Arc::clone(&counter),
        };

        // Chained Bind computation with 2 Bind layers
        let prog: Free<CloneCountingCmd, i32> = Free::suspend(cmd)
            .and_then(|n: i32| Free::pure(n + 1))
            .and_then(|n: i32| Free::pure(n * 2));

        counter.store(0, Ordering::SeqCst);

        let result = prog.run(|c| Arc::new(c.id as i32) as AnyValue);
        assert_eq!(result, 22);

        // Before optimization, `(**sub).clone()` cloned the inner subcomputation tree,
        // causing cmd to be cloned an extra time per Bind level (total 3).
        // With Arc::try_unwrap, the subcomputation is moved without cloning,
        // so cmd is cloned only once in into_any() and once in interp() (total 2).
        assert_eq!(counter.load(Ordering::SeqCst), 2);
    }

    #[test]
    fn test_free_error() {
        let err: FreeError<&str> = FreeError::Interpreter("boom");
        assert!(err.is_interpreter());
        assert!(!err.is_type_mismatch());
        assert_eq!(err.to_string(), "Free interpreter error: boom");

        let mismatch: FreeError<&str> = FreeError::TypeMismatch { expected: "i32" };
        assert!(mismatch.is_type_mismatch());
        assert!(!mismatch.is_interpreter());
        assert_eq!(
            mismatch.to_string(),
            "Free interpretation type mismatch: expected return type i32"
        );
    }

    #[test]
    fn test_anyvalue_pure_payload() {
        let val: AnyValue = Arc::new(42_i32);
        let prog: Free<TestCmd, AnyValue> = Free::pure(val);
        let res = prog.run(|_| Arc::new(()));
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_anyvalue_command_output() {
        let prog: Free<TestCmd, AnyValue> = Free::suspend(TestCmd::Fetch);
        let res = prog.run(|_| Arc::new(84_i32) as AnyValue);
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 84);
    }

    #[test]
    fn test_anyvalue_suspend_with() {
        let val: AnyValue = Arc::new(42_i32);
        let prog: Free<TestCmd, AnyValue> =
            Free::suspend_with(TestCmd::Fetch, move |_| Arc::clone(&val));
        let res = prog.run(|_| Arc::new(()));
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_anyvalue_bind_transformation() {
        let prog: Free<TestCmd, AnyValue> = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .and_then(|_| Free::pure(Arc::new(99_i32) as AnyValue));
        let res = prog.run(|_| Arc::new(()) as AnyValue);
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 99);
    }

    #[test]
    fn test_any_value_helper() {
        let val: AnyValue = any_value(42_i32);
        assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);

        let unit_val: AnyValue = any_value(());
        assert!(unit_val.downcast_ref::<()>().is_some());
    }

    #[test]
    fn test_then_semantic_equivalence() {
        use std::sync::atomic::{AtomicI32, Ordering};
        let p_then = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
            .then(Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
            .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        let p_bind = Free::<TestCmd, ()>::suspend(TestCmd::Increment(5))
            .and_then(|_| Free::<TestCmd, ()>::suspend(TestCmd::Increment(10)))
            .and_then(|_| Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        let state_then = Arc::new(AtomicI32::new(0));
        let s_t = Arc::clone(&state_then);
        let res_then: i32 = p_then.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                s_t.fetch_add(n, Ordering::SeqCst);
                any_value(())
            },
            TestCmd::Fetch => any_value(s_t.load(Ordering::SeqCst)),
        });

        let state_bind = Arc::new(AtomicI32::new(0));
        let s_b = Arc::clone(&state_bind);
        let res_bind: i32 = p_bind.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                s_b.fetch_add(n, Ordering::SeqCst);
                any_value(())
            },
            TestCmd::Fetch => any_value(s_b.load(Ordering::SeqCst)),
        });

        assert_eq!(res_then, 15);
        assert_eq!(res_bind, 15);
        assert_eq!(
            state_then.load(Ordering::SeqCst),
            state_bind.load(Ordering::SeqCst)
        );
    }

    #[test]
    fn test_then_is_then_not_bind() {
        let p1: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        let p2: Free<TestCmd, i32> = Free::suspend(TestCmd::Fetch);
        let chained = p1.then(p2);
        assert!(chained.is_then());
        assert!(!chained.is_bind());
        assert!(!chained.is_pure());
        assert!(!chained.is_suspend());
    }

    #[test]
    fn test_then_pure_shortcircuit() {
        let p_pure = Free::<TestCmd, ()>::pure(());
        let p_suspend = Free::<TestCmd, i32>::suspend(TestCmd::Fetch);
        let chained = p_pure.then(p_suspend);
        assert!(chained.is_suspend());
        assert!(!chained.is_then());
        assert_eq!(chained.as_suspend(), Some(&TestCmd::Fetch));
    }

    #[test]
    fn test_no_double_erasure_pure() {
        let val: AnyValue = any_value(42_i32);
        let prog: Free<TestCmd, AnyValue> = Free::pure(val);
        let erased: Free<TestCmd, AnyValue> = prog.into_any();
        let res = erased.run(|_| any_value(()));
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_no_double_erasure_then_chain() {
        let val: AnyValue = any_value(42_i32);
        let p1: Free<TestCmd, AnyValue> = Free::suspend(TestCmd::Fetch);
        let p2: Free<TestCmd, AnyValue> = Free::pure(val);
        let chain = p1.then(p2);
        let res = chain.run(|_| any_value(100_i32));
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 42);
    }

    #[test]
    fn test_then_construction_linearity() {
        let counter = Arc::new(AtomicUsize::new(0));
        let cmd = CloneCountingCmd {
            id: 1,
            clones: Arc::clone(&counter),
        };

        // Measure n = 1000
        counter.store(0, Ordering::SeqCst);
        let mut p1000: Free<CloneCountingCmd, ()> = Free::suspend(cmd.clone());
        for _ in 0..1000 {
            p1000 = p1000.then(Free::<CloneCountingCmd, ()>::suspend(cmd.clone()));
        }
        let clones_1000 = counter.load(Ordering::SeqCst);

        // Measure n = 2000
        counter.store(0, Ordering::SeqCst);
        let mut p2000: Free<CloneCountingCmd, ()> = Free::suspend(cmd.clone());
        for _ in 0..2000 {
            p2000 = p2000.then(Free::<CloneCountingCmd, ()>::suspend(cmd.clone()));
        }
        let clones_2000 = counter.load(Ordering::SeqCst);

        let ratio = clones_2000 as f64 / clones_1000 as f64;
        assert!(
            (1.8..=2.2).contains(&ratio),
            "Expected linear scaling (~2.0), got ratio: {ratio}"
        );
    }

    #[test]
    fn test_deep_then_drop() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        drop(p);
    }

    #[test]
    fn test_mixed_bind_then_drop() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for i in 0..20_000 {
            if i % 2 == 0 {
                p = p.then(Free::suspend(TestCmd::Increment(1)));
            } else {
                p = p.and_then(|_| Free::suspend(TestCmd::Increment(1)));
            }
        }
        drop(p);
    }

    #[test]
    fn test_deep_then_debug() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let debug_str = format!("{p:?}");
        assert!(debug_str.contains("Then(depth: 50000)"));
    }

    #[test]
    fn test_deep_then_run() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..25_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let mut count = 0;
        p.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                count += n;
                any_value(())
            },
            TestCmd::Fetch => any_value(count),
        });
        assert_eq!(count, 25_001);
    }

    #[test]
    fn test_then_clone_reuse() {
        let prog = Free::<TestCmd, ()>::suspend(TestCmd::Increment(7))
            .then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));

        let prog_clone = prog.clone();

        let mut c1 = 0;
        let r1: i32 = prog.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c1 += n;
                any_value(())
            },
            TestCmd::Fetch => any_value(c1),
        });

        let mut c2 = 100;
        let r2: i32 = prog_clone.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c2 += n;
                any_value(())
            },
            TestCmd::Fetch => any_value(c2),
        });

        assert_eq!(r1, 7);
        assert_eq!(r2, 107);
    }

    #[test]
    fn test_deep_then_drop_with_clones() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..30_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let q = p.clone();
        drop(q);
        drop(p);

        let mut p2: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..30_000 {
            p2 = p2.then(Free::suspend(TestCmd::Increment(1)));
        }
        let q2 = p2.clone();
        drop(p2);
        drop(q2);
    }

    #[test]
    fn test_accessors() {
        let p_pure: Free<TestCmd, i32> = Free::pure(42);
        assert!(p_pure.is_pure());
        assert_eq!(p_pure.as_pure(), Some(&42));
        assert_eq!(p_pure.as_suspend(), None);
        assert!(p_pure.as_then().is_none());

        let p_suspend: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(5));
        assert!(p_suspend.is_suspend());
        assert_eq!(p_suspend.as_suspend(), Some(&TestCmd::Increment(5)));
        assert_eq!(p_suspend.as_pure(), None);
        assert!(p_suspend.as_then().is_none());

        let p_then = p_suspend.then(Free::<TestCmd, i32>::suspend(TestCmd::Fetch));
        assert!(p_then.is_then());
        assert!(p_then.as_then().is_some());
        assert_eq!(p_then.as_pure(), None);
        assert_eq!(p_then.as_suspend(), None);

        let p_bind = p_suspend.and_then(|_| Free::pure(10));
        assert!(p_bind.is_bind());
        assert_eq!(p_bind.as_pure(), None);
        assert_eq!(p_bind.as_suspend(), None);
        assert!(p_bind.as_then().is_none());
    }

    #[test]
    fn test_monad_laws_effectful() {
        use std::sync::Mutex;
        let trace1 = Arc::new(Mutex::new(Vec::new()));
        let t1 = Arc::clone(&trace1);
        let f = |x: i32| {
            Free::<TestCmd, ()>::suspend(TestCmd::Increment(x)).and_then(move |_| Free::pure(x * 2))
        };

        // Left identity: pure(a).and_then(f) vs f(a)
        let left = Free::<TestCmd, i32>::pure(5).and_then(f);
        let right = f(5);

        let mut c1 = 0;
        let r_left = left.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c1 += n;
                t1.lock().unwrap().push(format!("inc({n})"));
                any_value(())
            },
            TestCmd::Fetch => any_value(c1),
        });

        let trace2 = Arc::new(Mutex::new(Vec::new()));
        let t2 = Arc::clone(&trace2);
        let mut c2 = 0;
        let r_right = right.run(|cmd| match cmd {
            TestCmd::Increment(n) => {
                c2 += n;
                t2.lock().unwrap().push(format!("inc({n})"));
                any_value(())
            },
            TestCmd::Fetch => any_value(c2),
        });

        assert_eq!(r_left, r_right);
        assert_eq!(*trace1.lock().unwrap(), *trace2.lock().unwrap());
    }

    #[test]
    fn test_mixed_bind_then_debug() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for i in 0..50_000 {
            p = if i % 2 == 0 {
                p.then(Free::suspend(TestCmd::Increment(1)))
            } else {
                p.and_then(|_| Free::suspend(TestCmd::Increment(1)))
            };
        }
        let debug_str = format!("{p:?}");
        assert!(!debug_str.is_empty());
    }

    #[test]
    fn test_zigzag_then_debug() {
        let x: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        let y: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(2));
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(0));
        for _ in 0..25_000 {
            p = x.clone().then(p).then(y.clone());
        }
        let debug_str = format!("{p:?}");
        assert!(!debug_str.is_empty());
    }

    #[test]
    fn test_const_fn_accessors() {
        const fn inspect_pure(x: &Free<u8, u8>) -> bool {
            x.is_pure()
        }
        const fn inspect_suspend(x: &Free<u8, u8>) -> bool {
            x.is_suspend()
        }
        const fn inspect_bind(x: &Free<u8, u8>) -> bool {
            x.is_bind()
        }
        const fn inspect_then(x: &Free<u8, u8>) -> bool {
            x.is_then()
        }
        const fn inspect_as_pure(x: &Free<u8, u8>) -> Option<&u8> {
            x.as_pure()
        }
        const fn inspect_as_suspend(x: &Free<u8, u8>) -> Option<&u8> {
            x.as_suspend()
        }

        let p: Free<u8, u8> = Free::pure(42);
        assert!(inspect_pure(&p));
        assert!(!inspect_suspend(&p));
        assert!(!inspect_bind(&p));
        assert!(!inspect_then(&p));
        assert_eq!(inspect_as_pure(&p), Some(&42));
        assert_eq!(inspect_as_suspend(&p), None);
    }
}
