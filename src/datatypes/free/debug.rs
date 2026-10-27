use core::fmt;

use alloc::sync::Arc;

use super::{AnyValue, Free, Node};

const MAX_DEBUG_RECURSION: usize = 8;
const MAX_SPINE_DEPTH: usize = 10;

struct DebugFree<'a, F, A>(&'a Free<F, A>, usize);

type SpineLink<F> = fn(&Node<F, AnyValue>) -> Option<&Arc<Free<F, AnyValue>>>;

// Counts consecutive `link` nodes starting at `cur`.
fn spine_len<F>(mut cur: &Free<F, AnyValue>, link: SpineLink<F>) -> usize {
    let mut len = 0;
    while let Some(next) = cur.node.as_ref().and_then(link) {
        len += 1;
        cur = next;
    }
    len
}

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
            let spine_depth = 1 + spine_len(sub, |node| match node {
                Node::Bind(next, _) => Some(next),
                _ => None,
            });
            if spine_depth > MAX_SPINE_DEPTH {
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
            let left_depth = 1 + spine_len(left, |node| match node {
                Node::Then(next, _) => Some(next),
                _ => None,
            });
            let right_depth = 1 + spine_len(right, |node| match node {
                Node::Then(_, next) => Some(next),
                _ => None,
            });

            let max_depth = left_depth.max(right_depth);
            if max_depth > MAX_SPINE_DEPTH {
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
