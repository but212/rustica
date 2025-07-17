use rustica::prelude::*;
use rustica::traits::composable::compose;
use std::fs::File;
use std::io::Read;

#[test]
fn understanding_monads() {
    // Create a monadic value
    let value = Maybe::Just(5);

    // Chain operations with bind
    let result = value.bind(|x| {
        if *x > 0 {
            Maybe::Just(x * 2)
        } else {
            Maybe::Nothing
        }
    });

    assert_eq!(result, Maybe::Just(10));
}

#[test]
fn working_with_maybe() {
    // Creating Maybe values
    let just_value = Maybe::Just(42);
    let nothing_value = Maybe::Nothing;
    let fallback_value = 0;

    // Transforming values
    let doubled = just_value.fmap(|x| x * 2);
    assert_eq!(doubled, Maybe::Just(84));

    // Default values
    let unwrap_or_default = nothing_value.unwrap_or(&fallback_value);
    assert_eq!(*unwrap_or_default, fallback_value);

    // Chaining operations
    let result = just_value
        .bind(|x| Maybe::Just(x.to_string()))
        .bind(|s| Maybe::Just(s.to_owned() + "!"));
    assert_eq!(result, Maybe::Just("42!".to_string()));
}

#[test]
fn working_with_either() {
    // Creating Either values
    let success: Either<String, i32> = Either::right(42);
    let failure: Either<String, i32> = Either::left("Error occurred".to_string());

    // Transforming values
    let doubled = success.fmap(|x| x * 2);
    assert_eq!(doubled, Either::right(84));

    // Handling errors
    let default_value = 0;
    let result = doubled.right_or(default_value);
    assert_eq!(result, 84);

    let error_result = failure.right_or(default_value);
    assert_eq!(error_result, 0);
}

#[test]
fn function_composition() {
    // Define simple functions
    let add_one = |x: i32| x + 1;
    let multiply_by_two = |x: i32| x * 2;

    // Compose functions
    let add_then_multiply = compose(add_one, multiply_by_two);

    // Use the composed function
    let result = add_then_multiply(5);
    assert_eq!(result, 12); // (5 + 1) * 2 = 12
}

#[test]
fn validating_user_input() {
    // Validation functions
    fn validate_length(input: &str) -> Maybe<String> {
        if input.len() >= 3 {
            Maybe::Just(input.to_string())
        } else {
            Maybe::Nothing
        }
    }

    fn validate_no_special_chars(input: &String) -> Maybe<String> {
        if input
            .chars()
            .all(|c| c.is_alphanumeric() || c.is_whitespace())
        {
            Maybe::Just(input.clone())
        } else {
            Maybe::Nothing
        }
    }
    let username = "John Doe";

    // Chain validations
    let validation_result = Maybe::Just(username.to_string())
        .bind(|s| validate_length(&s))
        .bind(validate_no_special_chars);

    match validation_result {
        Maybe::Just(valid_name) => println!("Valid username: {valid_name}"),
        Maybe::Nothing => println!("Invalid username"),
    }
}

#[test]
fn error_handling_with_either() {
    // Function that might fail
    fn read_file(path: &str) -> Either<String, String> {
        let mut file = match File::open(path) {
            Ok(file) => file,
            Err(e) => return Either::left(e.to_string()),
        };

        let mut contents = String::new();
        match file.read_to_string(&mut contents) {
            Ok(_) => Either::right(contents),
            Err(e) => Either::left(e.to_string()),
        }
    }

    // Try to read a file
    let file_contents = read_file("example.txt");

    // Transform the contents if reading succeeded
    let processed = file_contents.fmap(|contents| contents.lines().count());

    // Handle the result
    match processed {
        Either::Right(line_count) => println!("File has {line_count} lines"),
        Either::Left(error) => println!("Error reading file: {error}"),
    }
}

#[test]
fn monad_transformers() {
    // Define a state
    type Counter = i32;

    // Define a computation that increments the counter and returns a value
    fn increment_and_get(amount: i32) -> StateT<Counter, Maybe<(Counter, i32)>, i32> {
        StateT::new(move |s: Counter| {
            let new_state = s + amount;
            Maybe::Just((new_state, new_state))
        })
    }

    // Create a stateful computation
    let computation = increment_and_get(5).bind_with(
        |value| {
            // Use the value from the previous computation
            increment_and_get(value)
        },
        |m, f| m.bind(|v| f(*v)),
    );

    // Run the computation with an initial state
    let result = computation.run_state(0);

    // result is Maybe::Just((10, 10)) - our state went from 0 -> 5 -> 10
    match result {
        Maybe::Just((final_state, final_value)) => {
            println!("Final state: {final_state}, Final value: {final_value}");
        },
        Maybe::Nothing => println!("Computation failed"),
    }
}

#[test]
fn lenses() {
    // Define a data structure
    #[derive(Clone, Debug, PartialEq)]
    struct Person {
        name: String,
        age: i32,
    }

    // Define lenses for Person
    fn name_lens() -> Lens<Person, String, fn(&Person) -> String, fn(Person, String) -> Person> {
        Lens::new(
            |person: &Person| person.name.clone(),
            |person: Person, new_name: String| {
                let mut new_person = person; // clone() 필요 없음
                new_person.name = new_name;
                new_person
            },
        )
    }

    fn age_lens() -> Lens<Person, i32, fn(&Person) -> i32, fn(Person, i32) -> Person> {
        Lens::new(
            |person: &Person| person.age,
            |person: Person, new_age: i32| {
                let mut new_person = person;
                new_person.age = new_age;
                new_person
            },
        )
    }

    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };

    // Get a value using a lens
    let name = name_lens().get(&person);
    println!("Name: {name}");

    // Update a value using a lens
    let updated_person = age_lens().set(person.clone(), 31);
    println!("Updated age: {0}", updated_person.age);

    // Modify a value using a lens
    let older_person = age_lens().modify(person, |age| age + 5);
    println!("Age after 5 years: {0}", older_person.age);
}

#[cfg(feature = "pvec")]
#[test]
fn persistent_data_structures() {
    use rustica::pvec::{PersistentVector, pvec};
    // Create a vector using the macro
    let vec1 = pvec![1, 2, 3];

    // Create a new vector with an additional element
    let vec2 = vec1.push_back(4);

    // The original vector is unchanged
    assert_eq!(vec1.len(), 3);
    assert_eq!(vec2.len(), 4);

    // Update an element
    let vec3 = vec2.update(1, 20);
    assert_eq!(vec3.get(1), Some(&20));

    // Efficient for small vectors
    let small_vec = PersistentVector::from_slice(&[1, 2, 3]);

    // Pop the last element
    if let Some((new_vec, last)) = small_vec.pop_back() {
        assert_eq!(last, 3);
        assert_eq!(new_vec.len(), 2);
    }
}
