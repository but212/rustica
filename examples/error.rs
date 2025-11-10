use rustica::error::{
    ErrorPipeline, accumulate_context, format_error_chain, with_context_result,
    wrap_in_composable_result_boxed,
};

fn parse_config(content: &str) -> Result<i32, &'static str> {
    content.parse::<i32>().map_err(|_| "Invalid number format")
}

fn connect_db(timeout_ms: i32) -> Result<String, &'static str> {
    if timeout_ms < 100 {
        Err("Connection timeout too short")
    } else {
        Ok("db_connection_handle".to_string())
    }
}

fn process_data(connection: String, value: i32) -> Result<String, &'static str> {
    if value % 2 == 0 {
        Ok(format!("Processed {} rows via {}", value, connection))
    } else {
        Err("Value must be even number")
    }
}

fn main() {
    println!("=== Example 1: Correct Context Accumulation ===\n");

    let config_str = "not_a_number";

    let result = ErrorPipeline::new(wrap_in_composable_result_boxed(parse_config(config_str)))
        .with_context("Failed to parse configuration file")
        .and_then(|cfg| {
            with_context_result(connect_db(cfg), "DB connection attempt failed")
                .map_err(|mut e| {
                    *e = e.with_context("Error occurred during DB connection".to_string());
                    e
                })
                .map(|conn| (conn, cfg))
        })
        .and_then(|(connection, cfg)| {
            with_context_result(
                process_data(connection, cfg),
                "Error during data processing",
            )
            .map_err(|mut e| {
                *e = e.with_context("Failed to complete data processing pipeline".to_string());
                e
            })
        })
        .recover(|mut boxed_e| {
            *boxed_e = boxed_e.with_context("Recovery attempt initiated".to_string());
            Err(boxed_e)
        })
        .finish();

    match result {
        Ok(message) => println!("Success: {}", message),
        Err(err) => {
            println!("Error occurred:\n{}\n", format_error_chain(&err));
        },
    }

    println!("=== Example 2: Successful Pipeline ===\n");

    let config_str = "200";

    let result = ErrorPipeline::new(wrap_in_composable_result_boxed(parse_config(config_str)))
        .with_context("Failed to parse configuration file")
        .and_then(|cfg| {
            with_context_result(connect_db(cfg), "DB connection attempt failed")
                .map_err(|mut e| {
                    *e = e.with_context("Error occurred during DB connection".to_string());
                    e
                })
                .map(|conn| (conn, cfg))
        })
        .and_then(|(connection, cfg)| {
            with_context_result(
                process_data(connection, cfg),
                "Error during data processing",
            )
            .map_err(|mut e| {
                *e = e.with_context("Failed to complete data processing pipeline".to_string());
                e
            })
        })
        .finish();

    match result {
        Ok(message) => println!("Success: {}\n", message),
        Err(err) => {
            println!("Error occurred:\n{}\n", format_error_chain(&err));
        },
    }

    println!("=== Example 3: Bulk Context Accumulation ===\n");

    let operation_contexts = vec![
        "Loading user preferences",
        "Validating authentication token",
        "Establishing secure connection",
        "Executing transaction",
    ];

    let chained_error = accumulate_context(
        "Transaction failed: insufficient permissions",
        operation_contexts.into_iter(),
    );

    println!(
        "Bulk accumulated error analysis:\n{}",
        format_error_chain(&chained_error)
    );
}
