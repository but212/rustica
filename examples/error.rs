use rustica::error::{ContextError, accumulate_context, with_context_result};

/// Parses the configuration file contents as an `i32`.
///
/// # Errors
///
/// Returns an error if `content` is not a valid `i32`.
fn parse_config(content: &str) -> Result<i32, &'static str> {
    content.parse::<i32>().map_err(|_| "Invalid number format")
}

/// Opens a database connection with the given timeout.
///
/// # Errors
///
/// Returns an error if `timeout_ms` is below 100.
fn connect_db(timeout_ms: i32) -> Result<String, &'static str> {
    if timeout_ms < 100 {
        Err("Connection timeout too short")
    } else {
        Ok("db_connection_handle".to_string())
    }
}

/// Processes `value` rows over the given connection.
///
/// # Errors
///
/// Returns an error if `value` is odd.
fn process_data(connection: &str, value: i32) -> Result<String, &'static str> {
    if value % 2 == 0 {
        Ok(format!("Processed {value} rows via {connection}"))
    } else {
        Err("Value must be even number")
    }
}

/// Runs the configuration, connection, and processing stages in order.
///
/// # Errors
///
/// Returns the first failing stage's error, wrapped in a `ContextError` that carries that
/// stage's context.
fn run_pipeline(config_str: &str) -> Result<String, ContextError<&'static str>> {
    let cfg = with_context_result(
        parse_config(config_str),
        "Failed to parse configuration file",
    )?;
    let conn = with_context_result(connect_db(cfg), "DB connection attempt failed")?;
    let msg = with_context_result(process_data(&conn, cfg), "Error during data processing")?;
    Ok(msg)
}

fn main() {
    println!("=== Example 1: Context Accumulation on Failure ===\n");

    let config_str = "not_a_number";
    match run_pipeline(config_str) {
        Ok(message) => println!("Success: {message}"),
        Err(err) => println!("Error occurred:\n{}\n", err.error_chain()),
    }

    println!("=== Example 2: Successful Pipeline ===\n");

    let config_str = "200";
    match run_pipeline(config_str) {
        Ok(message) => println!("Success: {message}\n"),
        Err(err) => println!("Error occurred:\n{}\n", err.error_chain()),
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
        operation_contexts,
    );

    println!(
        "Bulk accumulated error analysis:\n{}",
        chained_error.error_chain()
    );
}
