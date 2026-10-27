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

#[cfg(test)]
mod tests {
    use alloc::format;

    use super::*;
    use crate::datatypes::free::fixtures::*;

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
    fn test_debug_bind_spine_beyond_limit_reports_depth() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..25 {
            p = p.and_then(|_| Free::suspend(TestCmd::Increment(1)));
        }
        assert_eq!(format!("{p:?}"), "Bind(depth: 25, \"<continuation>\")");
    }

    #[test]
    fn test_debug_right_then_spine_reports_depth() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..25 {
            p = Free::<TestCmd, ()>::suspend(TestCmd::Increment(1)).then(p);
        }
        assert_eq!(format!("{p:?}"), "Then(depth: 25)");
    }

    #[test]
    fn test_debug_short_spines_render_nested() {
        let first: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));

        let bind: Free<TestCmd, ()> = first.and_then(|_| Free::suspend(TestCmd::Increment(2)));
        assert_eq!(
            format!("{bind:?}"),
            "Bind(Suspend(Increment(1), \"<continuation>\"), \"<continuation>\")"
        );

        let then: Free<TestCmd, ()> = first.then(Free::suspend(TestCmd::Increment(2)));
        assert_eq!(
            format!("{then:?}"),
            "Then(Suspend(Increment(1), \"<continuation>\"), Suspend(Increment(2), \"<continuation>\"))"
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
    fn test_deep_then_debug() {
        let mut p: Free<TestCmd, ()> = Free::suspend(TestCmd::Increment(1));
        for _ in 0..50_000 {
            p = p.then(Free::suspend(TestCmd::Increment(1)));
        }
        let debug_str = format!("{p:?}");
        assert!(debug_str.contains("Then(depth: 50000)"));
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
}
