use alloc::vec::Vec;

use super::{AnyBox, Node, TryProgram};

// Iterative destruction.
fn drop_any_programs<H, E>(programs: impl IntoIterator<Item = TryProgram<H, AnyBox, E>>) {
    let mut pending = Vec::new();
    for mut program in programs {
        if let Some(node) = program.node.take() {
            pending.push(node);
        }
    }

    while let Some(node) = pending.pop() {
        match node {
            Node::Bind(mut sub, cont) => {
                if let Some(node) = sub.node.take() {
                    pending.push(node);
                }
                // Stack safety covers the explicit AST spine; captured closures may recurse on drop.
                drop(cont);
            },
            Node::Then(subs, mut next) => {
                for mut sub in subs {
                    if let Some(node) = sub.node.take() {
                        pending.push(node);
                    }
                }
                if let Some(node) = next.node.take() {
                    pending.push(node);
                }
            },
            Node::Pure(value) => drop(value),
            Node::Suspend(runner, cont) => drop((runner, cont)),
        }
    }
}

/// Iterative `Drop` implementation preventing stack overflows on deep un-evaluated chains.
///
/// Stack safety applies to explicit AST spines (`Then` and `Bind`), not closures capturing nested programs.
impl<H, A, E> Drop for TryProgram<H, A, E> {
    fn drop(&mut self) {
        let mut cur = self.node.take();
        while let Some(node) = cur {
            match node {
                Node::Then(subs, next) => {
                    drop_any_programs(subs);
                    let mut next = *next;
                    cur = next.node.take();
                },
                Node::Bind(sub, cont) => {
                    drop_any_programs([*sub]);
                    // Stack safety covers the explicit AST spine; captured closures may recurse on drop.
                    drop(cont);
                    return;
                },
                node => {
                    drop(node);
                    return;
                },
            }
        }
    }
}
