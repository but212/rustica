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

#[cfg(test)]
mod tests {
    use alloc::format;

    use super::*;
    use crate::datatypes::operational::Command;
    use crate::datatypes::operational::fixtures::*;

    #[test]
    fn test_predicates_and_debug() {
        let pure_p: Program<CalcInterpreter, i32> = Program::pure(42);
        assert!(pure_p.is_pure());
        assert!(!pure_p.is_suspend());
        assert!(!pure_p.is_bind());
        assert_eq!(format!("{pure_p:?}"), "Pure(42)");

        let susp_p: Program<CalcInterpreter, ()> = Add(1).suspend();
        assert!(!susp_p.is_pure());
        assert!(susp_p.is_suspend());
        assert!(!susp_p.is_bind());
        assert_eq!(format!("{susp_p:?}"), "Suspend(\"<command>\")");

        let bound_p = susp_p.and_then(|()| Program::pure(10));
        assert!(!bound_p.is_pure());
        assert!(!bound_p.is_suspend());
        assert!(bound_p.is_bind());
        assert_eq!(format!("{bound_p:?}"), "Bind(\"<sub-computation>\")");

        let and_then_p: Program<CalcInterpreter, i32> =
            Add(1).suspend().and_then(|()| Program::pure(10));
        assert!(and_then_p.is_bind());

        // TryProgram predicates
        let try_pure: TryProgram<FallibleCalc, i32, &str> = TryProgram::pure(99);
        assert!(try_pure.is_pure());
        assert!(!try_pure.is_suspend());
        assert!(!try_pure.is_bind());

        let try_susp: TryProgram<FallibleCalc, (), &str> = Add(1).try_suspend();
        assert!(try_susp.is_suspend());

        let try_bound = try_susp.and_then(|()| TryProgram::pure(100));
        assert!(try_bound.is_bind());

        let try_and_then: TryProgram<FallibleCalc, i32, &str> =
            Add(1).try_suspend().and_then(|()| TryProgram::pure(100));
        assert!(try_and_then.is_bind());
    }
}
