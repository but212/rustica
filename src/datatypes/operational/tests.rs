use alloc::string::ToString;
use alloc::vec;
use alloc::{format, string::String};

use super::*;

struct Add(i32);
impl Command for Add {
    type Output = ();
}

struct Multiply(i32);
impl Command for Multiply {
    type Output = ();
}

struct Fetch;
impl Command for Fetch {
    type Output = i32;
}

struct Stringify;
impl Command for Stringify {
    type Output = String;
}

struct CalcInterpreter {
    current: i32,
}

impl Handler<Add> for CalcInterpreter {
    fn handle(&mut self, cmd: Add) {
        self.current += cmd.0;
    }
}

impl Handler<Multiply> for CalcInterpreter {
    fn handle(&mut self, cmd: Multiply) {
        self.current *= cmd.0;
    }
}

impl Handler<Fetch> for CalcInterpreter {
    fn handle(&mut self, _cmd: Fetch) -> i32 {
        self.current
    }
}

impl Handler<Stringify> for CalcInterpreter {
    fn handle(&mut self, _cmd: Stringify) -> String {
        format!("Result: {}", self.current)
    }
}

#[test]
fn test_statically_typed_pipeline() {
    // Test Command::suspend extension method and Program::suspend
    let program: Program<CalcInterpreter, String> = Add(10)
        .suspend()
        .then(Multiply(3).suspend())
        .then(Fetch.suspend())
        .and_then(|num| Add(num).suspend()) // 30 + 30 = 60
        .then(Stringify.suspend());

    let mut interpreter = CalcInterpreter { current: 0 };
    let output = program.run(&mut interpreter);
    assert_eq!(output, "Result: 60");
}

#[test]
fn test_right_associated_then_preserves_order() {
    let program = Add(10)
        .suspend()
        .then(Multiply(3).suspend().then(Fetch.suspend()));

    let mut interpreter = CalcInterpreter { current: 0 };
    assert_eq!(program.run(&mut interpreter), 30);
}

#[test]
fn test_mixed_right_associated_then_and_then_preserves_order() {
    let program = Add(2).suspend().then(
        Fetch
            .suspend()
            .and_then(|value| Add(value).suspend())
            .then(Fetch.suspend()),
    );

    let mut interpreter = CalcInterpreter { current: 0 };
    assert_eq!(program.run(&mut interpreter), 4);
}

#[test]
fn test_nested_then_chunks_flatten_in_order() {
    // Non-commutative commands: any reordering of flattened prefixes changes the result.
    let program = Add(1)
        .suspend()
        .then(Multiply(3).suspend())
        .then(Add(2).suspend().then(Multiply(5).suspend()))
        .then(Fetch.suspend());

    let mut interpreter = CalcInterpreter { current: 0 };
    assert_eq!(program.run(&mut interpreter), 25);
}

#[test]
fn test_monad_laws() {
    // Left identity: pure(a).bind(f) == f(a)
    let a = 42;
    let f = |x: i32| Program::<CalcInterpreter, i32>::pure(x * 2);
    let left = Program::<CalcInterpreter, i32>::pure(a).and_then(f);
    let mut interp = CalcInterpreter { current: 0 };
    assert_eq!(left.run(&mut interp), 84);

    // Right identity: m.bind(pure) == m
    let m = Program::<CalcInterpreter, i32>::pure(100);
    let right = m.and_then(Program::pure);
    assert_eq!(right.run(&mut interp), 100);

    let m2 = Program::<CalcInterpreter, i32>::pure(100);
    assert_eq!(m2.and_then(Program::pure).run(&mut interp), 100);
}

#[test]
fn test_stack_safety_deep_chains() {
    // Unwinds 25,000 left-associated binds iteratively
    let mut p: Program<CalcInterpreter, ()> = Program::pure(());
    for _ in 0..25_000 {
        p = p.then(Add(1).suspend());
    }

    let mut interp = CalcInterpreter { current: 0 };
    p.run(&mut interp);
    assert_eq!(interp.current, 25_000);
}

#[test]
fn test_deep_chain_drop_stack_safety() {
    let mut p: Program<CalcInterpreter, ()> = Program::pure(());
    for _ in 0..50_000 {
        p = p.then(Add(1).suspend());
    }
    drop(p);
}

#[test]
fn test_deep_right_associated_chain_run_stack_safety() {
    let mut p: Program<CalcInterpreter, ()> = Program::pure(());
    for _ in 0..25_000 {
        p = Add(1).suspend().then(p);
    }

    let mut interp = CalcInterpreter { current: 0 };
    p.run(&mut interp);
    assert_eq!(interp.current, 25_000);
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

// Fallible tests
struct FallibleCalc {
    current: i32,
    should_fail: bool,
    fetches: usize,
}

impl TryHandler<Add, &'static str> for FallibleCalc {
    fn try_handle(&mut self, cmd: Add) -> Result<(), &'static str> {
        if self.should_fail {
            Err("overflow_simulated")
        } else {
            self.current += cmd.0;
            Ok(())
        }
    }
}

impl TryHandler<Fetch, &'static str> for FallibleCalc {
    fn try_handle(&mut self, _cmd: Fetch) -> Result<i32, &'static str> {
        self.fetches += 1;
        Ok(self.current)
    }
}

#[test]
fn test_try_program_success_and_failure() {
    let program: TryProgram<FallibleCalc, i32, &'static str> =
        Add(15).try_suspend().then(Fetch.try_suspend());

    let mut success_interp = FallibleCalc {
        current: 5,
        should_fail: false,
        fetches: 0,
    };
    assert_eq!(program.try_run(&mut success_interp), Ok(20));
    assert_eq!(success_interp.fetches, 1);

    let failing_program: TryProgram<FallibleCalc, i32, &'static str> = Fetch
        .try_suspend()
        .then(Add(15).try_suspend())
        .then(Fetch.try_suspend());

    let mut fail_interp = FallibleCalc {
        current: 5,
        should_fail: true,
        fetches: 0,
    };
    assert_eq!(
        failing_program.try_run(&mut fail_interp),
        Err("overflow_simulated")
    );
    assert_eq!(fail_interp.fetches, 1);
}

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

    let bound_p = susp_p.and_then(|_| Program::pure(10));
    assert!(!bound_p.is_pure());
    assert!(!bound_p.is_suspend());
    assert!(bound_p.is_bind());
    assert_eq!(format!("{bound_p:?}"), "Bind(\"<sub-computation>\")");

    let and_then_p: Program<CalcInterpreter, i32> =
        Add(1).suspend().and_then(|_| Program::pure(10));
    assert!(and_then_p.is_bind());

    // TryProgram predicates
    let try_pure: TryProgram<FallibleCalc, i32, &str> = TryProgram::pure(99);
    assert!(try_pure.is_pure());
    assert!(!try_pure.is_suspend());
    assert!(!try_pure.is_bind());

    let try_susp: TryProgram<FallibleCalc, (), &str> = Add(1).try_suspend();
    assert!(try_susp.is_suspend());

    let try_bound = try_susp.and_then(|_| TryProgram::pure(100));
    assert!(try_bound.is_bind());

    let try_and_then: TryProgram<FallibleCalc, i32, &str> =
        Add(1).try_suspend().and_then(|_| TryProgram::pure(100));
    assert!(try_and_then.is_bind());
}

#[test]
fn test_into_any_no_double_boxing() {
    let prog: Program<CalcInterpreter, i32> = Add(10)
        .suspend()
        .and_then(|_| Fetch.suspend())
        .and_then(|num| Program::pure(num * 2));

    let mut handler = CalcInterpreter { current: 5 };
    let res: i32 = prog.run(&mut handler);
    assert_eq!(res, 30); // (5 + 10) * 2
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

#[test]
fn test_anybox_pure_payload() {
    let val: Box<dyn Any> = Box::new(42_i32);
    let prog: Program<CalcInterpreter, Box<dyn Any>> = Program::pure(val);
    let mut calc = CalcInterpreter { current: 0 };
    let res = prog.run(&mut calc);
    assert_eq!(*res.downcast::<i32>().unwrap(), 42);
}

#[test]
fn test_anybox_command_output() {
    struct BoxCmd(i32);
    impl Command for BoxCmd {
        type Output = Box<dyn Any>;
    }
    struct BoxHandler;
    impl Handler<BoxCmd> for BoxHandler {
        fn handle(&mut self, cmd: BoxCmd) -> Box<dyn Any> {
            Box::new(cmd.0 * 2)
        }
    }
    let prog: Program<BoxHandler, Box<dyn Any>> = BoxCmd(21).suspend();
    let mut handler = BoxHandler;
    let res = prog.run(&mut handler);
    assert_eq!(*res.downcast::<i32>().unwrap(), 42);
}

#[test]
fn test_anybox_bind_transformation() {
    let prog: Program<CalcInterpreter, Box<dyn Any>> = Add(10)
        .suspend()
        .and_then(|_| Program::pure(Box::new(99_i32) as Box<dyn Any>));
    let mut calc = CalcInterpreter { current: 0 };
    let res = prog.run(&mut calc);
    assert_eq!(*res.downcast::<i32>().unwrap(), 99);
}

#[test]
fn test_const_fn_capability() {
    const fn prog_flags<H: 'static, A: 'static>(p: &Program<H, A>) -> (bool, bool, bool) {
        (p.is_pure(), p.is_suspend(), p.is_bind())
    }
    const fn try_prog_flags<H: 'static, A: 'static, E: 'static>(
        p: &TryProgram<H, A, E>,
    ) -> (bool, bool, bool) {
        (p.is_pure(), p.is_suspend(), p.is_bind())
    }

    const fn make_prog() -> Program<CalcInterpreter, i32> {
        Program::pure(42)
    }
    const fn make_try_prog() -> TryProgram<FallibleCalc, i32, &'static str> {
        TryProgram::pure(42)
    }

    assert_eq!(prog_flags(&make_prog()), (true, false, false));
    assert_eq!(try_prog_flags(&make_try_prog()), (true, false, false));
}

#[test]
fn test_rc_refcell_command_pipeline() {
    use alloc::rc::Rc;
    use core::cell::RefCell;

    struct LocalPushCmd(Rc<RefCell<Vec<i32>>>, i32);
    impl Command for LocalPushCmd {
        type Output = Rc<RefCell<Vec<i32>>>;
    }

    struct LocalHandler;
    impl Handler<LocalPushCmd> for LocalHandler {
        fn handle(&mut self, cmd: LocalPushCmd) -> Rc<RefCell<Vec<i32>>> {
            cmd.0.borrow_mut().push(cmd.1);
            cmd.0
        }
    }

    let shared = Rc::new(RefCell::new(vec![1]));
    let prog: Program<LocalHandler, Rc<RefCell<Vec<i32>>>> = LocalPushCmd(Rc::clone(&shared), 2)
        .suspend()
        .and_then(|rc| LocalPushCmd(rc, 3).suspend());

    let mut handler = LocalHandler;
    let result = prog.run(&mut handler);
    assert_eq!(*result.borrow(), vec![1, 2, 3]);
    assert_eq!(*shared.borrow(), vec![1, 2, 3]);
}

#[test]
fn test_rc_error_try_program() {
    use alloc::rc::Rc;

    struct FailCmd;
    impl Command for FailCmd {
        type Output = ();
    }

    struct FailHandler;
    impl TryHandler<FailCmd, Rc<String>> for FailHandler {
        fn try_handle(&mut self, _cmd: FailCmd) -> Result<(), Rc<String>> {
            Err(Rc::new("rc_err".to_string()))
        }
    }

    let prog: TryProgram<FailHandler, (), Rc<String>> = FailCmd.try_suspend();
    let mut handler = FailHandler;
    let res = prog.try_run(&mut handler);
    assert_eq!(res, Err(Rc::new("rc_err".to_string())));
}
