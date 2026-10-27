#![doc = include_str!("../../../docs/datatypes/free.md")]

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::any::Any;

mod debug;
mod error;

pub use error::FreeError;

/// Thread-safe type-erased value used in [`Free`] evaluation.
pub type AnyValue = Arc<dyn Any + Send + Sync>;

/// Wraps a value into an [`AnyValue`] for effect interpreter return values.
///
/// Avoids repeated `Arc::new(x) as AnyValue` boilerplate in [`Free::run`] and [`Free::try_run`].
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

/// Continuation function for the [`Free`] trampoline.
type ContFn<F> = Arc<dyn Fn(AnyValue) -> Free<F, AnyValue> + Send + Sync + 'static>;

/// Evaluation frame for iterative trampoline execution.
enum Frame<F> {
    BindCont(ContFn<F>),
    ThenNext(Arc<Free<F, AnyValue>>),
}

/// Internal AST node representation for [`Free`].
#[derive(Clone)]
enum Node<F, A> {
    /// Pure computation returning an immediate value.
    Pure(A),
    /// Suspended effect command with a continuation mapping interpreter output to `A`.
    Suspend(
        F,
        Arc<dyn Fn(AnyValue) -> Result<A, &'static str> + Send + Sync + 'static>,
    ),
    /// Dynamic sequencing: sub-computation followed by a continuation.
    Bind(
        Arc<Free<F, AnyValue>>,
        Arc<dyn Fn(AnyValue) -> Free<F, A> + Send + Sync + 'static>,
    ),
    /// Static sequencing: left sub-computation followed by right sub-computation.
    Then(Arc<Free<F, AnyValue>>, Arc<Free<F, AnyValue>>),
}

/// Computation tree separating AST construction from interpretation.
#[derive(Clone)]
#[repr(transparent)]
pub struct Free<F, A> {
    node: Option<Node<F, A>>,
}

#[inline]
fn unwrap_arc<T: Clone>(arc: Arc<T>) -> T {
    Arc::try_unwrap(arc).unwrap_or_else(|a| (*a).clone())
}

#[inline]
fn downcast_any_value<A: Clone + 'static>(any_val: &AnyValue) -> Option<A> {
    if core::any::TypeId::of::<A>() == core::any::TypeId::of::<AnyValue>() {
        let any_ref = any_val as &dyn Any;
        return any_ref.downcast_ref::<A>().cloned();
    }
    any_val.downcast_ref::<A>().cloned()
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

    /// Creates a pure computation returning `val`.
    #[inline]
    pub const fn pure(val: A) -> Self {
        Self::from_node(Node::Pure(val))
    }

    /// Suspends an effect command into a `Free` computation.
    ///
    /// The interpreter must return an [`AnyValue`] containing type `A`.
    ///
    /// # Panics
    ///
    /// Panics during [`run`](Self::run) if the interpreter return type does not match `A`.
    /// Use [`try_run`](Self::try_run) to handle mismatches as a `Result`.
    #[inline]
    pub fn suspend(effect: F) -> Self
    where
        A: Send + Sync + Clone + 'static,
    {
        Self::from_node(Node::Suspend(
            effect,
            Arc::new(|any_val: AnyValue| {
                downcast_any_value::<A>(&any_val).ok_or_else(core::any::type_name::<A>)
            }),
        ))
    }

    /// Suspends an effect command with a custom continuation.
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

    /// Converts this computation into a type-erased `Free<F, AnyValue>`.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    fn into_any(&self) -> Free<F, AnyValue>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
    {
        // Direct clone if already type-erased.
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

    /// Maps a function over the result value.
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

    /// Sequences a computation from the result of `self`.
    ///
    /// Evaluates `f(a)` immediately if `self` is pure. Otherwise, constructs a `Bind` node
    /// evaluated iteratively by the trampoline in [`run`](Self::run).
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
                        let a =
                            downcast_any_value::<A>(&any_val).expect("Free bind downcast failed");
                        f_arc(a)
                    }),
                ))
            },
        }
    }

    /// Sequences `next` after `self`, discarding `self`'s result.
    ///
    /// Constructs a value-independent `Then` AST node. If `self` is pure, returns `next`
    /// immediately without allocating.
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

    /// Applies a wrapped function in `self` to `value`.
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

    /// Combines `self` and `other` using a binary function.
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
    /// Internal iterative trampoline evaluating both [`run`](Self::run) and [`try_run`](Self::try_run).
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
                        return downcast_any_value::<A>(&val).ok_or(FreeError::TypeMismatch {
                            expected: core::any::type_name::<A>(),
                        });
                    },
                },
                Node::Suspend(cmd, cont) => {
                    let effect_res = interp(cmd).map_err(FreeError::Interpreter)?;
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
                            return downcast_any_value::<A>(&any_box).ok_or(
                                FreeError::TypeMismatch {
                                    expected: core::any::type_name::<A>(),
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
    /// Evaluates chains iteratively, keeping call stack depth $O(1)$.
    ///
    /// # Panics
    ///
    /// Panics if the interpreter returns an [`AnyValue`] that does not match type `A`.
    /// Use [`try_run`](Self::try_run) to handle interpreter mismatches as a `Result`.
    pub fn run<Interp>(&self, mut interp: Interp) -> A
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        Interp: FnMut(F) -> AnyValue,
    {
        match self.run_internal(|cmd| Ok::<_, core::convert::Infallible>(interp(cmd))) {
            Ok(val) => val,
            Err(FreeError::TypeMismatch { expected }) => {
                panic!("Free interpretation type mismatch: expected return type {expected}")
            },
            Err(FreeError::Interpreter(inf)) => match inf {},
        }
    }

    /// Evaluates the `Free` computation with a fallible effect interpreter.
    ///
    /// Returns `Err(FreeError::Interpreter(e))` on interpreter failure, or
    /// `Err(FreeError::TypeMismatch)` if the returned payload type does not match `A`.
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

    /// Returns `true` if this computation is a suspended leaf effect.
    #[inline]
    pub const fn is_suspend(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Suspend(_, _)))
    }

    /// Returns `true` if this computation is a dynamic continuation node (`Bind`).
    #[inline]
    pub const fn is_bind(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Bind(_, _)))
    }

    /// Returns `true` if this computation is a static sequencing node (`Then`).
    #[inline]
    pub const fn is_then(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Then(_, _)))
    }

    /// Returns a reference to the inner value if pure.
    #[inline]
    pub const fn as_pure(&self) -> Option<&A> {
        match self.node.as_ref() {
            Some(Node::Pure(a)) => Some(a),
            _ => None,
        }
    }

    /// Clones the inner value if pure.
    #[inline]
    pub fn to_pure(&self) -> Option<A>
    where
        A: Clone,
    {
        self.as_pure().cloned()
    }

    /// Returns a reference to the inner effect command if suspended.
    #[inline]
    pub const fn as_suspend(&self) -> Option<&F> {
        match self.node.as_ref() {
            Some(Node::Suspend(cmd, _)) => Some(cmd),
            _ => None,
        }
    }

    /// Returns references to the sub-computations if this is a `Then` node.
    #[inline]
    #[allow(clippy::type_complexity)]
    pub fn as_then(&self) -> Option<(&Free<F, AnyValue>, &Free<F, AnyValue>)> {
        match self.node.as_ref() {
            Some(Node::Then(left, right)) => Some((left.as_ref(), right.as_ref())),
            _ => None,
        }
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
mod tests;
