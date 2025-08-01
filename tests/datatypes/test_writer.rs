use rustica::datatypes::writer::Writer;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;

#[derive(Clone, Debug, PartialEq, Default)]
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
fn test_writer_creation_and_run() {
    // Test new
    let writer = Writer::new(Log(vec!["initial".to_string()]), 42);
    let (log, value) = writer.run();
    assert_eq!(value, 42);
    assert_eq!(log, Log(vec!["initial".to_string()]));

    // Test pure_value
    let writer_pure = Writer::<Log, _>::pure_value(100);
    let (log_pure, value_pure) = writer_pure.run();
    assert_eq!(value_pure, 100);
    assert_eq!(log_pure, Log::empty());
}

#[test]
fn test_writer_functor() {
    let writer = Writer::new(Log(vec!["initial".to_string()]), 42);

    // Test fmap
    let mapped = writer.fmap(|x| x * 2);
    let (log, value) = mapped.run();
    assert_eq!(value, 84);
    assert_eq!(log, Log(vec!["initial".to_string()]));

    // Test fmap_owned
    let mapped_owned = Writer::new(Log(vec!["initial".to_string()]), 42).fmap_owned(|x| x * 3);
    let (log_owned, value_owned) = mapped_owned.run();
    assert_eq!(value_owned, 126);
    assert_eq!(log_owned, Log(vec!["initial".to_string()]));
}

#[test]
fn test_writer_applicative() {
    // Create a Writer with a function that takes a reference to i32
    let writer_fn = Writer::new(Log(vec!["function created".to_string()]), |x: &i32| x * 2);
    // Create a Writer with a value
    let writer_val = Writer::new(Log(vec!["value created".to_string()]), 21);

    // Apply the function to the value (note: writer_fn.apply(&writer_val) is the correct order)
    let result = writer_fn.apply(&writer_val);
    let (log, value) = result.run();

    assert_eq!(value, 42);
    assert_eq!(
        log,
        Log(vec![
            "function created".to_string(),
            "value created".to_string(),
        ])
    );

    // Test lift2
    let add = |a: &i32, b: &i32| a + b;
    let writer1 = Writer::new(Log(vec!["first value".to_string()]), 10);
    let writer2 = Writer::new(Log(vec!["second value".to_string()]), 32);

    let result_lift = writer1.lift2(&writer2, add);
    let (log_lift, value_lift) = result_lift.run();

    assert_eq!(value_lift, 42);
    assert_eq!(
        log_lift,
        Log(vec!["first value".to_string(), "second value".to_string()])
    );
}

#[test]
fn test_writer_monad() {
    // Test bind
    let writer = Writer::new(Log(vec!["initial".to_string()]), 21);

    let bound = writer.bind(|x| Writer::new(Log(vec![format!("doubled {}", x)]), x * 2));

    let (log, value) = bound.run();
    assert_eq!(value, 42);
    assert_eq!(
        log,
        Log(vec!["initial".to_string(), "doubled 21".to_string()])
    );

    // Test chain
    let writer_chain = Writer::new(Log(vec!["start".to_string()]), 5)
        .bind(|x| Writer::new(Log(vec![format!("add 10 to {}", x)]), x + 10))
        .bind(|x| Writer::new(Log(vec![format!("multiply {} by 3", x)]), x * 3))
        .bind(|x| Writer::new(Log(vec![format!("subtract 3 from {}", x)]), x - 3));

    let (log_chain, value_chain) = writer_chain.run();
    assert_eq!(value_chain, 42);
    assert_eq!(
        log_chain,
        Log(vec![
            "start".to_string(),
            "add 10 to 5".to_string(),
            "multiply 15 by 3".to_string(),
            "subtract 3 from 45".to_string()
        ])
    );
}

#[test]
fn test_writer_tell() {
    // Create another writer with the same value but with a log
    let writer_with_log = Writer::new(Log(vec!["added a log".to_string()]), 10);

    let (log, value) = writer_with_log.run();
    assert_eq!(value, 10);
    assert_eq!(log, Log(vec!["added a log".to_string()]));
}

#[test]
fn test_writer_with_persistent_vector() {
    // Test that logs are accumulated properly using the persistent vector
    let writer1 = Writer::new(Log(vec!["log1".to_string()]), 10);

    // Map over the value, the log should remain the same
    let writer2 = writer1.fmap(|x| x + 1);

    // Add a new log entry by creating a new Writer with the same value
    let writer3 = Writer::new(Log(vec![format!("value is now {}", 11)]), 11);

    let (log1, value1) = writer1.run();
    let (log2, value2) = writer2.run();
    let (log3, value3) = writer3.run();

    assert_eq!(value1, 10);
    assert_eq!(log1, Log(vec!["log1".to_string()]));

    assert_eq!(value2, 11);
    assert_eq!(log2, Log(vec!["log1".to_string()]));

    assert_eq!(value3, 11);
    assert_eq!(log3, Log(vec![format!("value is now {}", 11)]));
}

#[test]
fn test_writer_complex_chaining() {
    // Create a function that logs and transforms a value
    fn process_number(n: &i32) -> Writer<Log, i32> {
        Writer::new(Log(vec![format!("processing {}", n)]), n * 2)
    }

    // Create a chain of Writer operations
    let start_writer = Writer::<Log, _>::pure_value(5);
    let intermediate_writer =
        start_writer.bind(|n| Writer::new(Log(vec!["starting with 5".to_string()]), *n));

    let result = intermediate_writer
        .bind(process_number)
        .bind(|n| Writer::new(Log(vec![format!("adding 10 to {}", n)]), n + 10))
        .fmap(|n| n * 2);

    let (log, value) = result.run();

    assert_eq!(value, 40); // ((5 * 2) + 10) * 2
    assert_eq!(
        log,
        Log(vec![
            "starting with 5".to_string(),
            "processing 5".to_string(),
            "adding 10 to 10".to_string(),
        ])
    );
}

// Test for Semigroup instance with String
#[test]
fn test_writer_semigroup() {
    use rustica::datatypes::wrapper::sum::Sum;
    // Test combining two writers
    let writer1 = Writer::new(Log(vec!["log1".to_string()]), Sum(15));
    let writer2 = Writer::new(Log(vec!["log2".to_string()]), Sum(27));

    let combined = writer1.combine(&writer2);
    let (log, value) = combined.run();

    assert_eq!(value.0, 42); // 15 + 27
    assert_eq!(log, Log(vec!["log1".to_string(), "log2".to_string()]));

    // Test combine_owned
    let writer3 = Writer::new(Log(vec!["log3".to_string()]), Sum(10));
    let writer4 = Writer::new(Log(vec!["log4".to_string()]), Sum(32));

    let combined_owned = writer3.combine_owned(writer4);
    let (log_owned, value_owned) = combined_owned.run();

    assert_eq!(value_owned.0, 42); // 10 + 32
    assert_eq!(log_owned, Log(vec!["log3".to_string(), "log4".to_string()]));
}
