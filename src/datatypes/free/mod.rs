#![doc = include_str!("../../../docs/datatypes/free.md")]

use alloc::sync::Arc;
use core::any::Any;

mod combinators;
mod debug;
mod error;
mod eval;
#[cfg(test)]
mod fixtures;
mod teardown;

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
pub fn any_value<T: Any + Send + Sync>(v: T) -> AnyValue {
    Arc::new(v)
}

/// Continuation of a `Bind` node, mapping interpreter output to the next computation.
type ContFn<F, A> = Arc<dyn Fn(AnyValue) -> Free<F, A> + Send + Sync + 'static>;

/// Combiner of a `Zip` node, joining the left and right interpreter outputs into `A`.
type ZipFn<A> = Arc<dyn Fn(AnyValue, AnyValue) -> A + Send + Sync + 'static>;

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
    Bind(Arc<Free<F, AnyValue>>, ContFn<F, A>),
    /// Static sequencing: left sub-computation followed by right sub-computation.
    Then(Arc<Free<F, AnyValue>>, Arc<Free<F, AnyValue>>),
    /// Independent combination: evaluates left, then right, then combines both results.
    Zip(Arc<Free<F, AnyValue>>, Arc<Free<F, AnyValue>>, ZipFn<A>),
}

/// Computation tree separating AST construction from interpretation.
#[derive(Clone)]
#[repr(transparent)]
pub struct Free<F, A> {
    node: Option<Node<F, A>>,
}

fn downcast_any_value<A: Clone + 'static>(any_val: &AnyValue) -> Option<A> {
    if core::any::TypeId::of::<A>() == core::any::TypeId::of::<AnyValue>() {
        let any_ref = any_val as &dyn Any;
        return any_ref.downcast_ref::<A>().cloned();
    }
    any_val.downcast_ref::<A>().cloned()
}

impl<F, A> Free<F, A> {
    const fn from_node(node: Node<F, A>) -> Self {
        Self { node: Some(node) }
    }

    /// # Panics
    ///
    /// Panics if the internal node has already been consumed.
    const fn node(&self) -> &Node<F, A> {
        self.node.as_ref().expect("Free node already consumed")
    }

    /// # Panics
    ///
    /// Panics if the internal node has already been consumed.
    const fn take_node(&mut self) -> Node<F, A> {
        self.node.take().expect("Free node already consumed")
    }

    /// Creates a pure computation returning `val`.
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
            Node::Zip(left, right, combine) => {
                let combine_clone = Arc::clone(combine);
                Free::from_node(Node::Zip(
                    Arc::clone(left),
                    Arc::clone(right),
                    Arc::new(move |x: AnyValue, y: AnyValue| {
                        Arc::new(combine_clone(x, y)) as AnyValue
                    }),
                ))
            },
        }
    }

    /// Returns `true` if this computation is a pure value.
    pub const fn is_pure(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Pure(_)))
    }

    /// Returns `true` if this computation is a suspended leaf effect.
    pub const fn is_suspend(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Suspend(_, _)))
    }

    /// Returns `true` if this computation is a dynamic continuation node (`Bind` or `Zip`).
    pub const fn is_bind(&self) -> bool {
        matches!(
            self.node.as_ref(),
            Some(Node::Bind(_, _) | Node::Zip(_, _, _))
        )
    }

    /// Returns `true` if this computation is a static sequencing node (`Then`).
    pub const fn is_then(&self) -> bool {
        matches!(self.node.as_ref(), Some(Node::Then(_, _)))
    }

    /// Returns a reference to the inner value if pure.
    pub const fn as_pure(&self) -> Option<&A> {
        match self.node.as_ref() {
            Some(Node::Pure(a)) => Some(a),
            _ => None,
        }
    }

    /// Clones the inner value if pure.
    pub fn to_pure(&self) -> Option<A>
    where
        A: Clone,
    {
        self.as_pure().cloned()
    }

    /// Returns a reference to the inner effect command if suspended.
    pub const fn as_suspend(&self) -> Option<&F> {
        match self.node.as_ref() {
            Some(Node::Suspend(cmd, _)) => Some(cmd),
            _ => None,
        }
    }

    /// Returns references to the sub-computations if this is a `Then` node.
    #[allow(clippy::type_complexity)]
    pub fn as_then(&self) -> Option<(&Free<F, AnyValue>, &Free<F, AnyValue>)> {
        match self.node.as_ref() {
            Some(Node::Then(left, right)) => Some((left.as_ref(), right.as_ref())),
            _ => None,
        }
    }
}

impl<F, A: Default> Default for Free<F, A> {
    fn default() -> Self {
        Self::pure(A::default())
    }
}

#[cfg(test)]
#[allow(clippy::missing_panics_doc)]
mod tests {
    use super::fixtures::*;
    use super::*;

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
    fn test_any_value_helper() {
        let val: AnyValue = any_value(42_i32);
        assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);

        let unit_val: AnyValue = any_value(());
        assert!(unit_val.downcast_ref::<()>().is_some());
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

        let p_bind = p_suspend.and_then(|()| Free::pure(10));
        assert!(p_bind.is_bind());
        assert_eq!(p_bind.as_pure(), None);
        assert_eq!(p_bind.as_suspend(), None);
        assert!(p_bind.as_then().is_none());
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
