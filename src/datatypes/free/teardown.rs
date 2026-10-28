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

    #[test]
    fn test_deep_then_drop() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        drop(p);
    }

    #[test]
    fn test_deep_right_nested_zip_with_drop() {
        let mut acc: Free<TestCmd, i32> = Free::pure(0);
        for _ in 0..50_000 {
            acc = Free::<TestCmd, i32>::suspend(TestCmd::Fetch).zip_with(acc, |a, b| a + b);
        }
        drop(acc);
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
}
