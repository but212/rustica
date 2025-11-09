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

    // Working with Maybe (like Option)
    let maybe_value = Maybe::Just(42);
    let doubled = maybe_value.fmap(|x| x * 2);
    assert_eq!(doubled.unwrap(), 84);

    // Working with Either for error handling
    let result: Either<String, &str> = Either::Right("success");
    let processed = result.fmap(|s| s.to_uppercase());
    assert_eq!(processed.unwrap(), "SUCCESS");

    // Using Choice for multiple alternatives
    let choices = Choice::new(1, [2, 3]);
    let results = choices.fmap(|x| x * 2);
    assert_eq!(results.iter().collect::<Vec<_>>(), vec![&2, &4, &6]);
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
