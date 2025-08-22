//! Demo of the new categorical utility functions
//!
//! This example demonstrates the category theory-inspired utility functions
//! that provide functional programming helpers for Rust's Option and Result types.

use rustica::utils::categorical_utils::*;

fn main() {
    println!("=== Categorical Utils Demo ===\n");

    // Functor-inspired mapping
    println!("1. Functor-inspired Mapping:");

    let maybe_num = Some(42);
    let maybe_string = map_option(maybe_num, |x| x.to_string());
    println!("map_option(Some(42), to_string) = {:?}", maybe_string);

    let maybe_none: Option<i32> = None;
    let still_none = map_option(maybe_none, |x| x.to_string());
    println!("map_option(None, to_string) = {:?}", still_none);

    let ok_result: Result<i32, &str> = Ok(10);
    let mapped_result = map_result(ok_result, |x| x * 2);
    println!("map_result(Ok(10), |x| x * 2) = {:?}", mapped_result);

    let err_result: Result<i32, &str> = Err("error");
    let still_err = map_result(err_result, |x| x * 2);
    println!("map_result(Err(\"error\"), |x| x * 2) = {:?}", still_err);

    println!();

    // Bimap for Result
    println!("2. Bimap for Result:");
    let success: Result<i32, &str> = Ok(42);
    let bimapped_success = bimap_result(success, |x| x * 2, |e| e.to_uppercase());
    println!(
        "bimap_result(Ok(42), |x| x * 2, uppercase) = {:?}",
        bimapped_success
    );

    let error: Result<i32, &str> = Err("error");
    let bimapped_error = bimap_result(error, |x| x * 2, |e| e.to_uppercase());
    println!(
        "bimap_result(Err(\"error\"), |x| x * 2, uppercase) = {:?}",
        bimapped_error
    );

    println!();

    // Monad-inspired chaining
    println!("3. Monad-inspired Chaining:");

    let safe_divide = |x: i32, y: i32| -> Option<i32> { if y != 0 { Some(x / y) } else { None } };

    let chain_result = flat_map_option(Some(20), |x| safe_divide(x, 4));
    println!(
        "flat_map_option(Some(20), safe_divide(_, 4)) = {:?}",
        chain_result
    );

    let chain_fail = flat_map_option(Some(10), |x| safe_divide(x, 0));
    println!(
        "flat_map_option(Some(10), safe_divide(_, 0)) = {:?}",
        chain_fail
    );

    let parse_and_double = |s: &str| -> Result<i32, &'static str> {
        s.parse::<i32>().map(|x| x * 2).map_err(|_| "parse error")
    };

    let chain_ok = flat_map_result(Ok("21"), parse_and_double);
    println!(
        "flat_map_result(Ok(\"21\"), parse_and_double) = {:?}",
        chain_ok
    );

    let chain_err = flat_map_result(Err("initial error"), parse_and_double);
    println!(
        "flat_map_result(Err(\"initial error\"), parse_and_double) = {:?}",
        chain_err
    );

    println!();

    // Function composition
    println!("4. Function Composition:");

    let add_one = |x: i32| x + 1;
    let double = |x: i32| x * 2;
    let composed = compose(add_one, double);

    println!("compose(add_one, double)(5) = {}", composed(5)); // (5 + 1) * 2 = 12

    println!();

    // Function argument flipping
    println!("5. Argument Flipping:");

    let subtract = |x: i32, y: i32| x - y;
    let flipped_subtract = flip(subtract);

    println!("subtract(10, 3) = {}", subtract(10, 3)); // 10 - 3 = 7
    println!("flip(subtract)(10, 3) = {}", flipped_subtract(10, 3)); // 3 - 10 = -7

    // Practical use case: creating different partial applications
    let divide = |x: f64, y: f64| x / y;
    let flipped_divide = flip(divide);
    let numbers = vec![8.0, 4.0, 2.0];
    let halved: Vec<f64> = numbers.iter().map(|x| flipped_divide(2.0, *x)).collect();
    println!("Halving {:?} = {:?}", numbers, halved);

    println!();

    // Collection utilities
    println!("6. Collection Utilities:");

    let strings = vec!["1", "not_a_number", "3", "4", "not_a_number"];
    let parsed_numbers = filter_map_collect(strings.iter(), |s| s.parse::<i32>().ok());
    println!("filter_map_collect(parse numbers) = {:?}", parsed_numbers);

    // Sequence Options
    let all_some = vec![Some(1), Some(2), Some(3)];
    let sequenced = sequence_options(all_some);
    println!(
        "sequence_options([Some(1), Some(2), Some(3)]) = {:?}",
        sequenced
    );

    let has_none = vec![Some(1), None, Some(3)];
    let failed_sequence = sequence_options(has_none);
    println!(
        "sequence_options([Some(1), None, Some(3)]) = {:?}",
        failed_sequence
    );

    // Sequence Results
    let all_ok: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
    let sequenced_results = sequence_results(all_ok);
    println!(
        "sequence_results([Ok(1), Ok(2), Ok(3)]) = {:?}",
        sequenced_results
    );

    let has_err: Vec<Result<i32, &str>> = vec![Ok(1), Err("error"), Ok(3)];
    let failed_results = sequence_results(has_err);
    println!(
        "sequence_results([Ok(1), Err(\"error\"), Ok(3)]) = {:?}",
        failed_results
    );

    println!();

    // Real-world example: Processing a pipeline of transformations
    println!("7. Real-world Pipeline Example:");

    let process_data = |input: &str| -> Option<String> {
        // Parse as number
        flat_map_option(input.parse::<i32>().ok(), |num| {
            // Ensure positive, then map to the final string.
            map_option((num > 0).then_some(num), |positive_num| {
                format!("Processed: {}", positive_num * 2)
            })
        })
    };

    let test_inputs = vec!["10", "-5", "not_a_number", "42"];
    for input in test_inputs {
        let result = process_data(input);
        println!("process_data(\"{}\") = {:?}", input, result);
    }

    println!("\n=== Demo Complete ===");
}
