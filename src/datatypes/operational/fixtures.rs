use alloc::format;
use alloc::string::String;

use super::{Command, Handler, TryHandler};

pub(super) struct Add(pub(super) i32);
impl Command for Add {
    type Output = ();
}

pub(super) struct Multiply(pub(super) i32);
impl Command for Multiply {
    type Output = ();
}

pub(super) struct Fetch;
impl Command for Fetch {
    type Output = i32;
}

pub(super) struct Stringify;
impl Command for Stringify {
    type Output = String;
}

pub(super) struct CalcInterpreter {
    pub(super) current: i32,
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

pub(super) struct FallibleCalc {
    pub(super) current: i32,
    pub(super) should_fail: bool,
    pub(super) fetches: usize,
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
