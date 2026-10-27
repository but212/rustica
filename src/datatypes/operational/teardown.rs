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

#[cfg(test)]
mod tests {
    use alloc::format;
    use alloc::string::{String, ToString};

    use crate::datatypes::operational::fixtures::*;
    use crate::datatypes::operational::{Command, Handler, Program};

    #[test]
    fn test_deep_chain_drop_stack_safety() {
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..50_000 {
            p = p.then(Add(1).suspend());
        }
        drop(p);
    }

    #[test]
    fn test_deep_right_associated_chain_drop_stack_safety() {
        let mut p: Program<CalcInterpreter, ()> = Program::pure(());
        for _ in 0..50_000 {
            p = Add(1).suspend().then(p);
        }
        drop(p);
    }

    #[test]
    fn test_deep_bind_chain_drop_stack_safety() {
        let mut p: Program<CalcInterpreter, i32> = Program::pure(0);
        for _ in 0..50_000 {
            p = p.and_then(|x| Fetch.suspend().map(move |y| x + y));
        }
        drop(p);
    }

    #[test]
    fn test_drop_releases_captured_values_once() {
        use alloc::rc::Rc;

        let shared = Rc::new(0_i32);
        let bind_capture = Rc::clone(&shared);
        let then_capture = Rc::clone(&shared);
        let suspend_capture = Rc::clone(&shared);
        let prog: Program<CalcInterpreter, i32> = Fetch
            .suspend()
            .and_then(move |x| Program::pure(x + *bind_capture))
            .then(Fetch.suspend().map(move |y| y + *then_capture))
            .then(Fetch.suspend().map(move |y| y + *suspend_capture));
        assert_eq!(Rc::strong_count(&shared), 4);
        drop(prog);
        assert_eq!(Rc::strong_count(&shared), 1);
    }

    #[test]
    fn test_operational_miri_ownership_and_drop() {
        struct StrCmd(String);
        impl Command for StrCmd {
            type Output = String;
        }
        struct StrHandler;
        impl Handler<StrCmd> for StrHandler {
            fn handle(&mut self, cmd: StrCmd) -> String {
                format!("{}_handled", cmd.0)
            }
        }

        // 1. Program dropped without running
        let prog = StrCmd("first".to_string())
            .suspend::<StrHandler>()
            .and_then(|s| StrCmd(format!("{s}_second")).suspend())
            .and_then(|s| Program::pure(format!("{s}_done")));
        drop(prog);

        // 2. Program run to completion
        let prog2 = StrCmd("init".to_string())
            .suspend()
            .and_then(|s| Program::pure(format!("{s}_mid")))
            .and_then(|s| StrCmd(s).suspend());
        let mut h = StrHandler;
        let res = prog2.run(&mut h);
        assert_eq!(res, "init_handled_mid_handled");
    }
}
