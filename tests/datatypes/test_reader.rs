use rustica::datatypes::reader::Reader;

#[test]
fn test_reader_environment_access() {
    // 1. Direct construction and running
    let r1 = Reader::new(|env: i32| env + 1);
    assert_eq!(r1.run_reader(10), 11);

    // 2. Accessing environment (ask/asks)
    let r_env = Reader::<String, String>::ask();
    let r_len = Reader::asks(|s: String| s.len());

    assert_eq!(r_env.run_reader("test".to_string()), "test");
    assert_eq!(r_len.run_reader("hello".to_string()), 5);
}

#[test]
fn test_reader_transformation_pipeline() {
    // Initial: Reads env and adds 1
    let base = Reader::new(|env: i32| env + 1);

    // 1. Functor: fmap (10 + 1) * 2 = 22
    let mapped = base.fmap(|x| x * 2);

    // 2. Monad: bind (22 * 10 = 220)
    let bound = mapped.bind(|x| Reader::new(move |env: i32| x * env));

    // 3. Environment isolation: local ((10 + 5 + 1) * 2 * (10 + 5) = 16 * 2 * 15 = 480)
    let localized = bound.local(|env| env + 5);

    assert_eq!(mapped.run_reader(10), 22);
    assert_eq!(bound.run_reader(10), 220);
    assert_eq!(localized.run_reader(10), 480);
}

#[test]
fn test_reader_combination() {
    let r1 = Reader::new(|env: i32| env + 10);
    let r2 = Reader::new(|env: i32| format!("val:{}", env));

    // Combine results from multiple readers
    let combined = r1.combine(&r2, |a, b| format!("{a}_{b}"));

    // (5 + 10) _ "val:5" = "15_val:5"
    assert_eq!(combined.run_reader(5), "15_val:5");
}
