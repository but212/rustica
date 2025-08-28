use rustica::utils::categorical_utils::*;

// This integration test is based on the "Real-world Pipeline Example" from the examples.
// It tests the composition of several categorical utility functions to achieve a practical goal.
#[test]
fn test_data_processing_pipeline() {
    let process_data = |input: &str| -> Option<String> {
        // 1. Parse the string to an integer Option
        let parsed = input.parse::<i32>().ok();

        // 2. Chain with flat_map_option to continue only if parsing was successful
        flat_map_option(parsed, |num| {
            // 3. Ensure the number is positive
            let positive_num = (num > 0).then_some(num);

            // 4. Map the positive number to a formatted string
            map_option(positive_num, |n| format!("Processed: {}", n * 2))
        })
    };

    // Test with valid input
    assert_eq!(process_data("10"), Some("Processed: 20".to_string()));
    assert_eq!(process_data("42"), Some("Processed: 84".to_string()));

    // Test with negative number (should be filtered out)
    assert_eq!(process_data("-5"), None);

    // Test with non-numeric input (parsing fails)
    assert_eq!(process_data("not_a_number"), None);

    // Test with zero (should be filtered out)
    assert_eq!(process_data("0"), None);
}
