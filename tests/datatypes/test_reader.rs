use rustica::datatypes::reader::Reader;

#[test]
fn test_reader_new_and_run() {
    // Reader that adds 1 to the environment (i32)
    let reader1: Reader<i32, i32> = Reader::new(|env: i32| env + 1);
    assert_eq!(reader1.run_reader(10), 11);

    // Reader that concatenates a string to the environment (String)
    let reader2: Reader<String, String> = Reader::new(|env: String| format!("{}-extra", env));
    assert_eq!(reader2.run_reader("hello".to_string()), "hello-extra");
}

#[test]
fn test_reader_ask() {
    // Use ask to get the environment directly
    let reader: Reader<String, String> = Reader::<String, String>::ask();
    assert_eq!(reader.run_reader("env1".to_string()), "env1");
    assert_eq!(reader.run_reader("env2".to_string()), "env2");
}

#[test]
fn test_reader_asks() {
    // Use asks to extract data from environment
    let reader: Reader<String, usize> = Reader::asks(|s: String| s.len());
    assert_eq!(reader.run_reader("hello".to_string()), 5);
    assert_eq!(reader.run_reader("world".to_string()), 5);
}

#[test]
fn test_reader_fmap() {
    let reader: Reader<i32, i32> = Reader::new(|env| env + 1); // Env -> 11
    let mapped_reader = reader.fmap(|x| x * 2); // Env -> (11 * 2) = 22
    assert_eq!(mapped_reader.run_reader(10), 22);

    // Chain fmap
    let mapped_reader2 = mapped_reader.fmap(|x| x - 5); // Env -> (22 - 5) = 17
    assert_eq!(mapped_reader2.run_reader(10), 17);
}

#[test]
fn test_reader_bind() {
    let reader: Reader<i32, i32> = Reader::new(|env| env + 1);

    // Bind to a function that produces a new Reader
    let bound_reader = reader.bind(|x| Reader::new(move |env: i32| x * env));

    // First reader gives 10 + 1 = 11
    // Second reader gives 11 * 10 = 110
    assert_eq!(bound_reader.run_reader(10), 110);

    // Chain binds
    let bound_reader2 = bound_reader.bind(|x| Reader::new(move |_env: i32| x / 2));

    // First: 10 + 1 = 11
    // Second: 11 * 10 = 110
    // Third: 110 / 2 = 55
    assert_eq!(bound_reader2.run_reader(10), 55);
}

#[test]
fn test_reader_local() {
    let reader: Reader<i32, i32> = Reader::new(|env| env * 2);

    // Use local to modify the environment
    let local_reader = reader.local(|env| env + 5);

    // Original: 10 * 2 = 20
    // Local: (10 + 5) * 2 = 30
    assert_eq!(reader.run_reader(10), 20);
    assert_eq!(local_reader.run_reader(10), 30);
}

#[test]
fn test_reader_combine() {
    let reader1: Reader<i32, i32> = Reader::new(|env| env + 10);
    let reader2: Reader<i32, String> = Reader::new(|env| format!("value: {}", env));

    // Combine the results of both readers
    let combined = reader1.combine(&reader2, |a, b| format!("{} and {}", a, b));

    // First: 5 + 10 = 15
    // Second: "value: 5"
    // Combined: "15 and value: 5"
    assert_eq!(combined.run_reader(5), "15 and value: 5");
}
