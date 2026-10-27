use alloc::vec::Vec;

use super::{AnyBox, Node, Steps, TryContFn, TryProgram};

enum TryFrame<H, E> {
    Bind(TryContFn<H, E>),
    Then(TryProgram<H, AnyBox, E>),
}

// Trampoline interpreter.
impl<H: 'static, A: 'static, E: 'static> TryProgram<H, A, E> {
    /// Evaluates the program using `handler` with stack safety.
    pub fn try_run(self, handler: &mut H) -> Result<A, E> {
        let mut cur: Node<H, AnyBox, E> = self.into_any().take_node();
        let mut stack: Vec<TryFrame<H, E>> = Vec::new();

        loop {
            let val = match cur {
                Node::Bind(mut sub, cont) => {
                    stack.push(TryFrame::Bind(cont));
                    cur = sub.take_node();
                    continue;
                },
                Node::Then(Steps { mut head, rest }, next) => {
                    stack.push(TryFrame::Then(*next));
                    for sub in rest.into_iter().rev() {
                        stack.push(TryFrame::Then(sub));
                    }
                    cur = head.take_node();
                    continue;
                },
                Node::Pure(val) => val,
                Node::Suspend(runner, cont) => cont(runner(handler)?),
            };

            match stack.pop() {
                Some(TryFrame::Bind(cont)) => {
                    cur = cont(val).take_node();
                },
                Some(TryFrame::Then(mut next)) => {
                    cur = next.take_node();
                },
                None => {
                    return Ok(*val
                        .downcast::<A>()
                        .expect("statically guaranteed final return type"));
                },
            }
        }
    }
}
