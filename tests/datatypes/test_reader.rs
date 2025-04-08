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
    // Use explicit type annotation for ask
    let reader: Reader<String, String> = Reader::<String, String>::ask();
    assert_eq!(reader.run_reader("env1".to_string()), "env1");
    assert_eq!(reader.run_reader("env2".to_string()), "env2");
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
    let reader_a: Reader<String, usize> = Reader::new(|env: String| env.len()); // Env = "hello" => 5

    // Function for bind: takes usize, returns a new Reader
    let f = |len: usize| -> Reader<String, String> {
        Reader::new(move |env: String| {
            format!("Env '{}' has length {}", env, len)
        })
    };

    let bound_reader = reader_a.bind(f);
    // Run with env "hello"
    // 1. reader_a runs: returns 5
    // 2. f(5) runs: returns Reader::new(|env| format!("Env '{}' has length 5", env))
    // 3. The new reader runs with "hello": returns "Env 'hello' has length 5"
    assert_eq!(bound_reader.run_reader("hello".to_string()), "Env 'hello' has length 5");
}
