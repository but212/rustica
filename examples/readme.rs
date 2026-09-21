#[cfg(feature = "pvec")]
fn pvec_example() {
    use rustica::pvec::pvec;

    let v1 = pvec![1, 2, 3, 4, 5];
    let v2 = v1.push_back(6);
    let v3 = v1.update(0, 10);

    assert_eq!(v1.get(0), Some(&1));
    assert_eq!(v2.get(5), Some(&6));
    assert_eq!(v3.get(0), Some(&10));
}

fn basic_usage() {
    use rustica::prelude::*;

    // Working with Option using Functor trait
    let opt_value = Some(42);
    let doubled = opt_value.fmap(|x| x * 2);
    assert_eq!(doubled, Some(84));

    // Working with Result using Functor trait
    let result: Result<&str, String> = Ok("success");
    let processed = result.fmap(|s| s.to_uppercase());
    assert_eq!(processed, Ok("SUCCESS".to_string()));

    // Choice: guaranteed non-empty priority/fallback execution
    let endpoints = Choice::new("primary.api.com", ["backup1.api.com", "backup2.api.com"]);
    assert_eq!(*endpoints.primary(), "primary.api.com");
    let connected = endpoints.try_each(|ep| {
        if *ep == "backup1.api.com" {
            Ok("connected")
        } else {
            Err("unreachable")
        }
    });
    assert_eq!(connected, Ok("connected"));

    // Using Validated for error accumulation
    let v1: Validated<i32, &str> = Validated::valid(10);
    let v2: Validated<i32, &str> = Validated::valid(20);
    let sum = Validated::<i32, &str>::lift2(|a, b| a + b, v1, v2);
    assert_eq!(sum, Validated::valid(30));
}

fn operational_monad_example() {
    use rustica::datatypes::operational::{Command, Handler};

    struct Add(i32);
    impl Command for Add {
        type Output = ();
    }
    struct Get;
    impl Command for Get {
        type Output = i32;
    }

    struct Calc(i32);
    impl Handler<Add> for Calc {
        fn handle(&mut self, cmd: Add) {
            self.0 += cmd.0;
        }
    }
    impl Handler<Get> for Calc {
        fn handle(&mut self, _cmd: Get) -> i32 {
            self.0
        }
    }

    let program = Add(5).suspend().then(Add(10).suspend()).then(Get.suspend());
    let mut calc = Calc(0);
    let result = program.run(&mut calc);
    assert_eq!(result, 15);
}

fn free_monad_example() {
    use rustica::datatypes::free::{AnyValue, Free};
    use std::sync::Arc;

    #[derive(Clone, Debug, PartialEq)]
    enum Cmd {
        Log(&'static str),
    }

    let program: Free<Cmd, ()> =
        Free::<Cmd, ()>::suspend(Cmd::Log("step1")).then(Free::suspend(Cmd::Log("step2")));
    let mut logs = Vec::new();
    program.run(|cmd| {
        match cmd {
            Cmd::Log(msg) => logs.push(msg),
        }
        Arc::new(()) as AnyValue
    });
    assert_eq!(logs, vec!["step1", "step2"]);
}

fn main() {
    #[cfg(feature = "pvec")]
    pvec_example();
    basic_usage();
    operational_monad_example();
    free_monad_example();
}
