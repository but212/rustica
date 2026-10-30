use alloc::sync::Arc;

use super::{AnyValue, Free, Node, downcast_any_value};

impl<F, A> Free<F, A> {
    /// Maps a function over the result value.
    ///
    /// Evaluates `f(a)` immediately if `self` is pure. Otherwise, constructs a `Bind` node
    /// evaluated iteratively by the trampoline in [`run`](Self::run).
    pub fn map<B, Func>(&self, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A) -> B + Send + Sync + 'static,
    {
        self.and_then(move |a| Free::pure(f(a)))
    }

    /// Sequences a computation from the result of `self`.
    ///
    /// Evaluates `f(a)` immediately if `self` is pure. Otherwise, constructs a `Bind` node
    /// evaluated iteratively by the trampoline in [`run`](Self::run).
    ///
    /// # Panics
    ///
    /// The resulting `Free` AST node does not panic during normal evaluation; downcast
    /// failure is prevented by static type invariants.
    pub fn and_then<B, Next>(&self, f: Next) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Next: Fn(A) -> Free<F, B> + Send + Sync + 'static,
    {
        if let Node::Pure(a) = self.node() {
            f(a.clone())
        } else {
            let sub = Arc::new(self.to_any());
            Free::from_node(Node::Bind(
                sub,
                Arc::new(move |any_val: AnyValue| {
                    let a = downcast_any_value::<A>(&any_val).expect("Free bind downcast failed");
                    f(a)
                }),
            ))
        }
    }

    /// Sequences `next` after `self`, discarding `self`'s result.
    ///
    /// Constructs a value-independent `Then` AST node. If `self` is pure, returns `next`
    /// immediately without allocating.
    pub fn then<B>(&self, next: Free<F, B>) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
    {
        if self.is_pure() {
            return next;
        }
        let left = Arc::new(self.to_any());
        let right = Arc::new(next.to_any());
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
        self.zip_with(value, |f, t| f(t))
    }

    /// Combines `self` and `other` using a binary function.
    ///
    /// If `self` is pure, maps `other` directly without creating a `Zip` node. Otherwise,
    /// constructs a `Zip` AST node that owns both sub-computations rather than capturing
    /// them in a continuation.
    pub fn zip_with<T2, B, Func>(&self, other: Free<F, T2>, f: Func) -> Free<F, B>
    where
        F: Send + Sync + Clone + 'static,
        A: Send + Sync + Clone + 'static,
        T2: Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        Func: Fn(A, T2) -> B + Send + Sync + 'static,
    {
        if let Some(a) = self.as_pure() {
            let a = a.clone();
            return other.map(move |b| f(a.clone(), b));
        }
        let left = Arc::new(self.to_any());
        let right = Arc::new(other.to_any());
        Free::from_node(Node::Zip(
            left,
            right,
            Arc::new(move |x: AnyValue, y: AnyValue| {
                let a = downcast_any_value::<A>(&x).expect("Free zip downcast failed");
                let b = downcast_any_value::<T2>(&y).expect("Free zip downcast failed");
                f(a, b)
            }),
        ))
    }
}

#[cfg(test)]
#[allow(clippy::missing_panics_doc, clippy::cast_precision_loss)]
mod tests {
    use core::sync::atomic::Ordering;

    use super::*;
    use crate::datatypes::free::any_value;
    use crate::datatypes::free::fixtures::*;

    #[test]
    fn test_apply_and_zip_with() {
        let func: Free<TestCmd, fn(i32) -> i32> = Free::pure(|x: i32| x + 10);
        let val: Free<TestCmd, i32> = Free::pure(5);
        let applied = func.apply(val);
        assert_eq!(applied.to_pure(), Some(15));

        let fa: Free<TestCmd, i32> = Free::pure(3);
        let fb: Free<TestCmd, i32> = Free::pure(4);
        let combined: Free<TestCmd, i32> = fa.zip_with(fb, |a, b| a * b);
        assert_eq!(combined.to_pure(), Some(12));

        let fa2: Free<TestCmd, i32> = Free::pure(3);
        let fb2: Free<TestCmd, i32> = Free::pure(4);
        let zipped = fa2.zip_with(fb2, |a, b| a + b);
        assert_eq!(zipped.to_pure(), Some(7));
    }

    #[test]
    fn test_zip_with_suspended_left_is_bind_not_then() {
        let zipped: Free<TestCmd, i32> = Free::<TestCmd, i32>::suspend(TestCmd::Fetch)
            .zip_with(Free::<TestCmd, i32>::pure(1), |a, b| a + b);
        assert!(zipped.is_bind());
        assert!(!zipped.is_then());
        assert!(!zipped.is_pure());
    }

    #[test]
    fn test_monad_laws() {
        // Left identity: pure(a).bind(f) == f(a)
        let a = 7;
        let f = |x: i32| Free::pure(x * 3);
        let left: Free<TestCmd, i32> = Free::pure(a).and_then(f);
        let right = f(a);
        assert_eq!(left.to_pure(), right.to_pure());

        // Right identity: m.bind(pure) == m
        let m: Free<TestCmd, i32> = Free::pure(42);
        let bound = m.and_then(Free::pure);
        assert_eq!(bound.to_pure(), Some(42));
        assert_eq!(m.and_then(Free::pure).to_pure(), Some(42));

        // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
        let g = |x: i32| Free::pure(x + 100);
        let m1: Free<TestCmd, i32> = Free::pure(5);
        let m2: Free<TestCmd, i32> = Free::pure(5);
        let r1 = m1.and_then(f).and_then(g);
        let r2 = m2.and_then(move |x| f(x).and_then(g));
        assert_eq!(r1.to_pure(), r2.to_pure());
    }

    #[test]
    fn test_anyvalue_bind_transformation() {
        let prog: Free<TestCmd, AnyValue> = Free::<TestCmd, ()>::suspend(TestCmd::Increment(10))
            .and_then(|()| Free::pure(Arc::new(99_i32) as AnyValue));
        let res = prog.run(|_| Arc::new(()) as AnyValue);
        assert_eq!(*res.downcast_ref::<i32>().unwrap(), 99);
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
        let (cmd, counter) = counting_cmd(1);

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
}
