use rustica::datatypes::writer::Writer;
use rustica::prelude::*;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;

#[derive(Clone, Debug, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct Log(Vec<String>);

impl Semigroup for Log {
    fn combine(&self, other: &Self) -> Self {
        let mut combined = self.0.clone();
        combined.extend(other.0.clone());
        Log(combined)
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut combined = self.0;
        combined.extend(other.0);
        Log(combined)
    }
}

impl Monoid for Log {
    fn empty() -> Self {
        Log(Vec::new())
    }
}

#[test]
fn test_writer_lifecycle_and_mapping() {
    // 1. Creation and pure values
    let w1 = Writer::new(Log(vec!["init".into()]), 42);
    let w_pure = Writer::<Log, _>::pure_value(100);

    assert_eq!(w1.clone().run(), (Log(vec!["init".into()]), 42));
    assert_eq!(w_pure.run(), (Log::empty(), 100));

    // 2. Mapping values while preserving logs (Functor)
    let mapped = w1.fmap(|x| x * 2);
    assert_eq!(mapped.run(), (Log(vec!["init".into()]), 84));
}

#[test]
fn test_writer_accumulation_modes() {
    // 1. Applicative (Horizontal accumulation)
    let w_fn = Writer::new(Log(vec!["f".into()]), |x: &i32| x * 2);
    let w_val = Writer::new(Log(vec!["v".into()]), 21);
    let app_res = w_fn.apply(&w_val);

    assert_eq!(app_res.run(), (Log(vec!["f".into(), "v".into()]), 42));

    // 2. Monad (Vertical/Sequential accumulation)
    let monad_res = Writer::new(Log(vec!["step1".into()]), 10)
        .bind(|x| Writer::new(Log(vec![format!("step2:{}", x)]), x + 5));

    assert_eq!(
        monad_res.run(),
        (Log(vec!["step1".into(), "step2:10".into()]), 15)
    );
}

#[test]
fn test_writer_composition_scenarios() {
    // 1. Complex Chaining Pipeline
    let pipeline = Writer::<Log, _>::pure_value(5)
        .bind(|n| Writer::new(Log(vec!["start".into()]), *n))
        .bind(|n| Writer::new(Log(vec!["double".into()]), n * 2))
        .bind(|n| Writer::new(Log(vec!["plus10".into()]), n + 10))
        .fmap(|n| n * 2);

    let (log, val) = pipeline.run();
    assert_eq!(val, 40); // ((5 * 2) + 10) * 2
    assert_eq!(log.0.len(), 3);

    // 2. Direct Semigroup Combination
    use rustica::datatypes::wrapper::sum::Sum;
    let w1 = Writer::new(Log(vec!["l1".into()]), Sum(15));
    let w2 = Writer::new(Log(vec!["l2".into()]), Sum(27));

    let combined = w1.combine(&w2);
    assert_eq!(
        combined.run(),
        (Log(vec!["l1".into(), "l2".into()]), Sum(42))
    );
}

#[cfg(feature = "serde")]
#[test]
fn test_writer_serde() {
    use serde_json;
    let writer = Writer::new(Log(vec!["log".into()]), 42);
    let json = serde_json::to_string(&writer).unwrap();
    let back: Writer<Log, i32> = serde_json::from_str(&json).unwrap();
    assert_eq!(writer, back);
}
