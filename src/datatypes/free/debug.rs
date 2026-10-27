use core::fmt;

use super::{AnyValue, Free, Node};

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
