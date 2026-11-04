use alloc::sync::Arc;
use alloc::vec::Vec;

use super::{AnyValue, Free, Node};

impl<F, A> Free<F, A> {
    fn push_node_children(node: Node<F, A>, stack: &mut Vec<Arc<Free<F, AnyValue>>>) {
        match node {
            Node::Pure(_) | Node::Suspend(_, _) => {},
            Node::Bind(sub, _) => {
                stack.push(sub);
            },
            Node::Then(left, right) | Node::Zip(left, right, _) => {
                stack.push(right);
                stack.push(left);
            },
        }
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
    use crate::datatypes::free::fixtures::*;

    #[test]
    fn test_deep_free_drop_with_clones() {
        let p = then_chain(30_000);
        let q = p.clone();
        // Drop clone first, then original
        drop(q);
        drop(p);

        // Now drop original first, then clone
        let p2 = then_chain(30_000);
        let q2 = p2.clone();
        drop(p2);
        drop(q2);
    }

    #[test]
    fn test_deep_then_drop() {
        drop(then_chain(50_000));
    }

    #[test]
    fn test_deep_right_nested_zip_with_drop() {
        drop(right_zip_chain(50_000));
    }

    #[test]
    fn test_deep_right_nested_apply_drop() {
        let mut acc: Free<TestCmd, i32> = Free::pure(0);
        for _ in 0..50_000 {
            let func: Free<TestCmd, fn(i32) -> i32> = Free::suspend(TestCmd::Fetch);
            acc = func.apply(acc);
        }
        drop(acc);
    }

    #[test]
    fn test_mixed_bind_then_drop() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for i in 0..20_000 {
            if i % 2 == 0 {
                p = p.then(Free::suspend(TestCmd::Increment(1)));
            } else {
                p = p.and_then(|()| Free::suspend(TestCmd::Increment(1)));
            }
        }
        drop(p);
    }

    #[test]
    fn test_deep_map_on_suspend_drop() {
        drop(map_chain(50_000));
    }

    #[test]
    fn test_deep_pure_left_zip_with_suspend_drop() {
        drop(pure_left_zip_chain(50_000));
    }

    /// Small-depth ownership checks for the Miri CI job (deep chains are too slow under Miri).
    #[test]
    fn test_free_miri_ownership_and_drop() {
        use alloc::sync::Arc;

        use crate::datatypes::free::any_value;

        const DEPTH: usize = 64;

        // Deep chains: drop in both clone/original orders.
        let p = then_chain(DEPTH);
        let q = p.clone();
        drop(q);
        drop(p);
        let p = then_chain(DEPTH);
        let q = p.clone();
        drop(p);
        drop(q);
        drop(right_zip_chain(DEPTH));
        drop(map_chain(DEPTH));
        drop(pure_left_zip_chain(DEPTH));

        // Captured values are released exactly once across drop, clone-drop, and run.
        let shared = Arc::new(0_i32);
        let build = || {
            let (bind_capture, zip_capture) = (Arc::clone(&shared), Arc::clone(&shared));
            Free::<TestCmd, ()>::suspend(TestCmd::Increment(1))
                .and_then(move |()| Free::pure(*bind_capture))
                .zip_with(
                    Free::<TestCmd, i32>::suspend(TestCmd::Fetch),
                    move |a, b| a + b + *zip_capture,
                )
        };

        let prog = build();
        assert_eq!(Arc::strong_count(&shared), 3);
        let clone = prog.clone();
        drop(prog);
        assert_eq!(Arc::strong_count(&shared), 3);
        drop(clone);
        assert_eq!(Arc::strong_count(&shared), 1);

        let result = build().run(|cmd| match cmd {
            TestCmd::Increment(_) => any_value(()),
            TestCmd::Fetch => any_value(1_i32),
        });
        assert_eq!(result, 1);
        assert_eq!(Arc::strong_count(&shared), 1);
    }
}
