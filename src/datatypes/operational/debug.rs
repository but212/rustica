use core::fmt;

use super::{Node, Program, TryProgram};

impl<H, A: fmt::Debug> fmt::Debug for Program<H, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

// Non-recursive Debug implementation summarizing sub-computations without traversing children.
impl<H, A: fmt::Debug, E> fmt::Debug for TryProgram<H, A, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.node {
            Some(Node::Pure(a)) => f.debug_tuple("Pure").field(a).finish(),
            Some(Node::Suspend(_, _)) => f.debug_tuple("Suspend").field(&"<command>").finish(),
            Some(Node::Bind(_, _) | Node::Then(_, _)) => {
                f.debug_tuple("Bind").field(&"<sub-computation>").finish()
            },
            None => f.debug_tuple("Consumed").finish(),
        }
    }
}
