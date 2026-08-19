use rustica::error::{accumulate_context, format_error_chain, with_context_result};

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

fn process_data(connection: &str, value: i32) -> Result<String, &'static str> {
    if value % 2 == 0 {
        Ok(format!("Processed {} rows via {}", value, connection))
    } else {
        Err("Value must be even number")
    }
}

fn run_pipeline(
    config_str: &str,
) -> Result<String, Box<rustica::error::ComposableError<&'static str>>> {
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
        Ok(message) => println!("Success: {}", message),
        Err(err) => println!("Error occurred:\n{}\n", format_error_chain(&err)),
    }

    println!("=== Example 2: Successful Pipeline ===\n");

    let config_str = "200";
    match run_pipeline(config_str) {
        Ok(message) => println!("Success: {}\n", message),
        Err(err) => println!("Error occurred:\n{}\n", format_error_chain(&err)),
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
        format_error_chain(&chained_error)
    );
}
