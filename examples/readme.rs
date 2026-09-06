fn pvec_example() {
    use rustica::pvec::PersistentVector;
    use rustica::pvec::pvec;

    let v1: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];
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

    // Using Choice for guaranteed non-empty alternatives
    let choices = Choice::new(1, [2, 3]);
    let results = choices.fmap(|x| x * 2);
    assert_eq!(results.into_iter().collect::<Vec<_>>(), vec![2, 4, 6]);

    // Using Validated for error accumulation
    let v1: Validated<&str, i32> = Validated::valid(10);
    let v2: Validated<&str, i32> = Validated::valid(20);
    let sum = Validated::<&str, i32>::lift2(|a, b| a + b, v1, v2);
    assert_eq!(sum, Validated::valid(30));
}

fn state_management() {
    use rustica::datatypes::state::State;

    // A simple counter
    let counter = State::new(|count: i32| (count + 1, count));

    // Run the state computation
    let (new_count, result) = counter.run_state(0);
    assert_eq!(new_count, 1);
    assert_eq!(result, 0);
}

fn io_operations() {
    use rustica::datatypes::io::IO;

    // Pure IO description
    let read_line = IO::new(|| "Hello from IO!".to_string());

    // Execute the IO operation
    let result = read_line.run();
    assert_eq!(result, "Hello from IO!");
}

fn main() {
    pvec_example();
    basic_usage();
    state_management();
    io_operations();
}
